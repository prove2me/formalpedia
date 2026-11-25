-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.exists_clm_of_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:05:10.24134+00:00
-- url     : https://prove2.me/submissions/fbd67988-5211-458b-ab10-c9c5478b0a42

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExistsClmOfI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open Metric Set Filter Topology Complex
open scoped ContDiff
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} (A : V n →L[ℝ] ℂ) (hA : ∀ w : V n, A (I • w) = I * A w) :
    ∃ g' : V n →L[ℂ] ℂ, g'.restrictScalars ℝ = A := by
  refine ⟨{ toFun := A, map_add' := A.map_add, map_smul' := fun c w => ?_, cont := A.continuous }, ?_⟩
  · simp only [RingHom.id_apply, smul_eq_mul]
    conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul,
      A.map_add, A.map_smul, A.map_smul, hA]
    conv_rhs => rw [← Complex.re_add_im c]
    simp only [Complex.real_smul]
    ring
  · exact ContinuousLinearMap.ext fun w => rfl
end ReciprocityTheory.L2DbarEstimates.C
