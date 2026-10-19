-- Prove2me | solution 1 for QuantumParallelRepetition.posSemidef_mul_spectralSupportProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/109daa82-ad04-4f43-87a2-d7390ca1e972

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_mul_spectralSupportProjection
import Theorems.Thm_QuantumParallelRepetition_posSemidef_kernel_of_sub_posSemidef

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {d : Type*} [Fintype d] [DecidableEq d]
    {F A : Matrix d d ℂ}
    (hF : F.PosSemidef) (hA : A.PosSemidef)
    (hsub : (F - A).PosSemidef) :
    A * spectralSupportProjection F hF = A := by
  let P := spectralSupportProjection F hF
  have hFP : F * P = F := mul_spectralSupportProjection F hF
  have hkernel : F * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hFP, sub_self]
  have hAzero : A * (1 - P) = 0 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    have hxi : F *ᵥ ((1 - P) *ᵥ Pi.single i 1) = 0 := by
      have h := congrArg
        (fun M : Matrix d d ℂ => M *ᵥ Pi.single i 1) hkernel
      simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using h
    have hAi := posSemidef_kernel_of_sub_posSemidef hA hsub hxi
    simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using hAi
  have hdiff : A - A * P = 0 := by
    simpa [mul_sub] using hAzero
  exact (sub_eq_zero.mp hdiff).symm
end QuantumParallelRepetition
