-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceVerifier_historyBorn_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/a08c5ba8-ca00-422b-a95a-c32950073b94

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceVerifier_historyBorn_bounds

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
          (actual h j)) :=
  (unconditionalActualFairSourceVerifier_historyBorn_bounds
    G n S D a₀ b₀ actual actual_row_mass h).1
end QuantumParallelRepetition
