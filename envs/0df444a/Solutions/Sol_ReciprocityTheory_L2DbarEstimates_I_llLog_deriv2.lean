-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.llLog_deriv2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:48:23.025814+00:00
-- url     : https://prove2.me/submissions/ccfa41cc-7ff9-4043-99ee-56ea6616dfe9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_llLog_deriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : -c / 2 < t) :
    deriv (deriv (llLog c)) t = -((t + c) ^ 2)⁻¹ := by
  have hev : deriv (llLog c) =ᶠ[𝓝 t] fun s => (s + c)⁻¹ := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact llLog_deriv hc hs
  rw [hev.deriv_eq]
  have hpos : t + c ≠ 0 := by linarith
  have h1 := ((hasDerivAt_id t).add_const c).inv hpos
  have h2 : HasDerivAt (fun s => (s + c)⁻¹) (-((t + c) ^ 2)⁻¹) t := by
    convert h1 using 1 <;> first | rfl | (simp [div_eq_mul_inv])
  exact h2.deriv
end ReciprocityTheory.L2DbarEstimates.I
