From Coq Require Import
     Morphisms
     Setoid
     RelationClasses
     ZArith
.


(*rewriting with eq*)

Local Open Scope Z_scope.

Goal forall (a b c d : Z), a = b -> b = c -> c = d -> a = d.
Proof.
  intros a b c d Hab Hbc Hcd. rewrite Hab. rewrite Hbc. auto.
Qed.

Goal forall (a b c x y z : Z), a = x -> b = y -> c = z -> 
                                           a + b + c = x + y + z.
Proof.
  intros a b c x y z Hax Hby Hcz. rewrite Hax. rewrite Hby. rewrite Hcz.
  reflexivity.
Qed.

Section ModularArith.
  
  Context (k : Z).

  Definition equiv (n m : Z) : Prop := exists (x y : Z), n + x * k = m + y * k.

  Notation "a ≡ b" := (equiv a b) (at level 70).

  Ltac invert_ex := 
    repeat match goal with | H : ex _ _ |- _ => destruct H as [?x ?Hx] end.

  Instance trans_equiv : Transitive equiv.
  Proof.
    red. unfold equiv. intros.
    destruct H as [n0 [m0 Hnm0] ]. destruct H0 as [n1 [m1 Hnm1] ].
      assert (Hy  : y = x + n0 * k - (m0 * k)); try omega.
      assert (Hfact : n0 * k - m0 * k = (n0 - m0) * k); try ring.
      rewrite <- Z.add_sub_assoc in Hy. rewrite Hfact in Hy.
      rewrite Hy in Hnm1. exists (n0 -m0 + n1). exists m1.
      rewrite <- Hnm1. ring.
  Qed.

  Goal forall (a b c : Z), a ≡ b -> b ≡ c -> a ≡ c.
  Proof.
    intros. rewrite H. Fail (rewrite <- H).
    auto.
  Qed.

  Instance sym_equiv : Symmetric equiv.
  Proof. 
    red. intros. destruct H as [n [m Hnm] ]. exists m. exists n. omega.
  Qed.

  Goal forall (a b c : Z), a ≡ b -> b ≡ c -> a ≡ c.
  Proof.
    intros. rewrite H. rewrite <- H. rewrite <- H0.
    rewrite H0. rewrite H. auto.
  Qed.

  Instance equiv_equiv : Equivalence equiv.
  Proof.
    constructor. all: try apply trans_equiv; try apply sym_equiv; try unfold equiv; red; intros.
    exists 0. exists 0. auto.
  Qed.

  Goal forall (a b c d : Z), a ≡ b -> b ≡ c -> c ≡ d -> a ≡ d.
  Proof.
    intros a b c d Hab Hcb Hcd. rewrite Hab. rewrite Hcb. auto.
  Qed.

  Lemma k_equiv_0 : k ≡ 0.
  Proof.
    exists 0. exists 1. ring.
  Qed.

  Goal forall x, x + k ≡ x.
  Proof.
    intros. Fail rewrite k_equiv_0. Abort.

  Print Proper.

  Goal Proper equiv 2.
  Proof.
    red. reflexivity.
  Qed.

  Locate "==>".
  
  Print respectful.

  Goal Proper (equiv ==> equiv) (fun x => x + 2).
  Proof.
    intros ? ? ?.
    unfold equiv in *. destruct H. destruct H. exists x0. exists x1. omega.
  Qed. 

  Goal Proper ((fun x y => x > y) ==> equiv) (fun x => x + 2).
  Proof.
    intros ? ? ?. Abort.
  (*
fun (A B : U) (R : relation A) (R' : relation B) (f g : A -> B) =>     
forall x y : A, R x y -> R' (f x) (g y)
     : forall A B : Type, relation A -> relation B -> relation (A -> B)

*)

  Instance add_proper_r {x: Z} : Proper (equiv ==> equiv) (Z.add x).
  Proof.
    intros y z H. unfold equiv in *.
    destruct H as [n [m Hnm] ]. exists n. exists m. 
    omega.
  Qed.


  Goal forall x, x + k ≡ x.
  Proof.
    intros. rewrite k_equiv_0.
    rewrite Z.add_comm. simpl. reflexivity.
  Qed.

  Goal forall x, k + x ≡ x.
  Proof.
    intros. 
    Fail rewrite k_equiv_0. 
  Abort.  

  Instance add_proper : Proper (equiv ==> equiv ==> equiv) Z.add.
  Proof.
    intros x y  Hxy z w Hzw.
    rewrite <- Hzw. Fail rewrite Hxy. 
    rewrite Z.add_comm. rewrite Hxy. rewrite Z.add_comm.
    reflexivity.
  Qed.
  

  Goal forall x, k + x ≡ x.
  Proof.
    intros. 
    rewrite k_equiv_0. reflexivity.
  Qed.

  Goal forall x : Z, k + x ≡ k + x + k.
  Proof.
    intros. rewrite k_equiv_0. simpl. 
    rewrite Z.add_comm. reflexivity.
  Qed.

 Goal forall x : Z, k + (x + ( k + k ) + k) ≡ k + k + (k + k) + ( (k + k) + (k + k)  ) + x. 
   Proof.
     intros. rewrite k_equiv_0. simpl. rewrite Z.add_comm. simpl.
     rewrite Z.add_comm. reflexivity.
   Qed.

End ModularArith.

Section StateMonad.

  Context (S : Type).
  
  Definition State (A : Type) := S -> (S * A).

  Definition ret {A} (a : A) := fun s : S => (s,a).

  Definition bind {A B} (m : State A) (f : A -> State B) :=
    fun s => let '(s',a) := m s in f a s'.

   Notation "m >>= f" := (bind m f) (at level 70).

  Definition state_eq {A : Type} (m1 m2 : State A) :=
    forall (s : S), m1 s = m2 s.

  Notation "m1 ≈ m2" := (state_eq m1 m2) (at level 70).

  Instance state_eq_equiv {A : Type} : Equivalence (@state_eq A).
  Proof.
    constructor; red; intros; red; intros; auto.
    rewrite H. auto.
  Qed.

  Lemma bind_ret : forall (A B : Type) (a : A) (f : A -> State B),
        ret a >>= f ≈ f a.
    intros. red. intros. cbn. auto.
  Qed.

  Lemma ret_bind : forall (A : Type) (m : State A),
      m >>= ret ≈ m.
  Proof.
    intros. red. intros. cbv. destruct (m s). auto.
  Qed.

  Lemma bind_bind : forall (A B C : Type) (m : State A) 
                           (f : A -> State B) (g : B -> State C),
      (m >>= f) >>= g ≈ (m >>= (fun a => f a >>= g)).
  Proof.
    intros. red. intros. cbv. destruct (m s). auto.
  Qed.
      

  Print pointwise_relation.

  Instance proper_monad {A B: Type} : Proper (@state_eq A ==> pointwise_relation A state_eq ==> @state_eq B) (bind).
  Proof.
    repeat intro. rename x0 into f. rename y0 into g.
    rename x into m1. rename y into m2. red in H0. red in H0.
    red in H. cbv. rewrite H.
    destruct (m2 s).
    apply H0.
  Qed.

  Goal forall (A B :Type) (a : A) (f : A -> State B),
      ret a >>= (fun a' => f a') >>= ret ≈ f a.
  Proof.
    intros. rewrite bind_bind. rewrite bind_ret. rewrite ret_bind.
    reflexivity.
  Qed.

End StateMonad.
