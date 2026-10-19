-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceVerifier_isPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/c4a7cec7-5c60-4823-b05e-3e37fb192bcf

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_matrixEffectCLM_isPositive
import Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierEffect_tensor_posSemidef
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualLocalPOVMWinningEffect_posSemidef

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
    {P N L m : ℕ} (j : Fin L) (x : X) (y : Y) :
    (integratorActualC485WinningEffect
      (P := P) (N := N) (m := m)
      G n S D a₀ b₀ j x y).IsPositive := by
  classical
  unfold integratorActualC485WinningEffect
  apply matrixEffectCLM_isPositive
  apply unconditionalMatchedVerifierEffect_tensor_posSemidef
  exact unconditionalActualLocalPOVMWinningEffect_posSemidef
    G
    (integratorActualC485SelectedAlicePOVM
      G n S D a₀ P N m x)
    (integratorActualC485SelectedBobPOVM
      G n S D b₀ P N m y) x y
end QuantumParallelRepetition
