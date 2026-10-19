-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceVerifier_historyBorn_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/ba51a7f3-34ff-4000-95d5-15d503971526

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceVerifier_born_nonnegative
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceVerifier_born_le_mass

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ}
    (actual : (h : ExactLocallySampleableTuple X Y A B D) →
      (j : Fin L) →
      IntegratorActualC485BranchSpace
        1 P N
          (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
          L m j)
    (actual_row_mass :
      ∀ h : ExactLocallySampleableTuple X Y A B D,
        (∑ j : Fin L, ‖actual h j‖ ^ 2) ≤ 1)
    (h : ExactLocallySampleableTuple X Y A B D) :
    0 ≤
      (∑ j : Fin L,
        quadraticExpectation
          (integratorActualC485WinningEffect
            (P := P) (N := N) (m := m)
            G n S D a₀ b₀ j h.2.1 h.2.2.1)
          (actual h j)) ∧
      (∑ j : Fin L,
        quadraticExpectation
          (integratorActualC485WinningEffect
            (P := P) (N := N) (m := m)
            G n S D a₀ b₀ j h.2.1 h.2.2.1)
          (actual h j)) ≤ 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro j _
    exact unconditionalActualFairSourceVerifier_born_nonnegative
      G n S D a₀ b₀ j h.2.1 h.2.2.1 (actual h j)
  · calc
      _ ≤ ∑ j : Fin L, ‖actual h j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact unconditionalActualFairSourceVerifier_born_le_mass
          G n S D a₀ b₀ j h.2.1 h.2.2.1 (actual h j)
      _ ≤ 1 := actual_row_mass h
end QuantumParallelRepetition
