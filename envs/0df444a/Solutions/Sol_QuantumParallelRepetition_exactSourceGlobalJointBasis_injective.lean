-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceGlobalJointBasis_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/ff4842db-4d36-44a1-9948-f71f4dba8982

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    Function.Injective (exactSourceGlobalJointBasis G n S D r) := by
  intro i j same
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  have alice := congrArg Prod.fst same
  have bob := congrArg Prod.snd same
  change
    (Sum.inr ⟨r, .inr (.inl ia)⟩ :
      ExactGlobalHistoryLocalIndex G n S D) =
      Sum.inr ⟨r, .inr (.inl ja)⟩ at alice
  change
    (Sum.inr ⟨r, .inr (.inr ib)⟩ :
      ExactGlobalHistoryLocalIndex G n S D) =
      Sum.inr ⟨r, .inr (.inr jb)⟩ at bob
  have alice_block :
      (Sum.inr (.inl ia) : ExactPaddedLocalIndex G n S D r) =
        Sum.inr (.inl ja) :=
    eq_of_heq (Sigma.mk.inj (Sum.inr.inj alice)).2
  have bob_block :
      (Sum.inr (.inr ib) : ExactPaddedLocalIndex G n S D r) =
        Sum.inr (.inr jb) :=
    eq_of_heq (Sigma.mk.inj (Sum.inr.inj bob)).2
  have alice' : ia = ja :=
    Sum.inl.inj (Sum.inr.inj alice_block)
  have bob' : ib = jb :=
    Sum.inr.inj (Sum.inr.inj bob_block)
  exact Prod.ext alice' bob'
end QuantumParallelRepetition
