-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceVerifier_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/8abe9c45-5420-4356-9a93-3671737bd196

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierEffect_tensor_norm_le_one
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualLocalPOVMWinningEffect_posSemidef
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualLocalPOVMWinningEffect_complement_posSemidef

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
    ‖integratorActualC485WinningEffect
      (P := P) (N := N) (m := m)
      G n S D a₀ b₀ j x y‖ ≤ 1 := by
  classical
  unfold integratorActualC485WinningEffect
  apply unconditionalMatchedVerifierEffect_tensor_norm_le_one
  · exact unconditionalActualLocalPOVMWinningEffect_posSemidef
      G
      (integratorActualC485SelectedAlicePOVM
        G n S D a₀ P N m x)
      (integratorActualC485SelectedBobPOVM
        G n S D b₀ P N m y) x y
  · exact unconditionalActualLocalPOVMWinningEffect_complement_posSemidef
      G
      (integratorActualC485SelectedAlicePOVM
        G n S D a₀ P N m x)
      (integratorActualC485SelectedBobPOVM
        G n S D b₀ P N m y) x y
end QuantumParallelRepetition
