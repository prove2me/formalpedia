-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.gs_sq_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:50:34.528836+00:00
-- url     : https://prove2.me/submissions/1ace3cce-b7a2-4004-ab34-a5d7e10a39c0

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_norm_sq_le_pow_gs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
open Finset InnerProductSpace ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
theorem _root_.solution (b : Fin d → E) (hr : IsRed b) (m : ℝ) (hm : ∀ i, m ≤ ‖b i‖ ^ 2) (j : Fin d) :
    m / 2 ^ (d - 1) ≤ ‖gs b j‖ ^ 2 := by
  have h1 := norm_sq_le_pow_gs b hr j
  have h2 := hm j
  have hjd : j.val ≤ d - 1 := by have := j.isLt; omega
  have hp : (2:ℝ) ^ j.val ≤ 2 ^ (d - 1) := pow_le_pow_right₀ (by norm_num) hjd
  have hpos : (0:ℝ) < 2 ^ (d - 1) := by positivity
  rw [div_le_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg ‖gs b j‖)]
end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
