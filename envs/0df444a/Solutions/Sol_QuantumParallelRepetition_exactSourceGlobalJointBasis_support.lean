-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceGlobalJointBasis_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/39a3f164-8897-4f6c-9ac5-ecce1dad72c6

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
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r))
    (j : ExactGlobalHistoryLocalIndex G n S D ×
      ExactGlobalHistoryLocalIndex G n S D)
    (outside : ∀ i, exactSourceGlobalJointBasis
      G n S D r i ≠ j) :
    exactGlobalHistoryVector G n S D r
      (exactPaddedVector G n S D r z) j = 0 := by
  classical
  rcases j with ⟨u, v⟩
  rcases u with u | ⟨ru, u⟩
  · rfl
  rcases v with v | ⟨rv, v⟩
  · rfl
  change
    (if ha : ru = r then
      if hb : rv = r then
        exactPaddedVector G n S D r z
          (ha ▸ u, hb ▸ v)
      else 0
    else 0) = 0
  by_cases hu : ru = r
  · subst ru
    by_cases hv : rv = r
    · subst rv
      simp only [dite_true]
      rcases u with u | (u | u)
      · rfl
      · rcases v with v | (v | v)
        · rfl
        · rfl
        · exact False.elim
            (outside (u, v)
              (by rfl))
      · rfl
    · simp only [dif_neg hv, dite_true]
  · simp only [dif_neg hu]
end QuantumParallelRepetition
