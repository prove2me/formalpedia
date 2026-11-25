-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_smoothR_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:23:41.720503+00:00
-- url     : https://prove2.me/submissions/16a497ec-ae41-4758-b15c-48561a1c957d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_smoothR_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_smoothR_sum


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
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ) (hph : SmoothR n z ph) (r : ℝ) :
    SmoothR n z (ev n g ph r) := by
  have h1 : SmoothR n z (fun x => ∑ i ∈ Finset.univ, ‖g i x‖ ^ 2) :=
    smoothR_sum n z _ _ (fun i _ => Smooth.normSq n z _ (Holo.smooth n z _ (hg i)))
  have h2 : SmoothR n z (fun x => Real.exp (-ph x)) :=
    SmoothR.comp n z (fun t => Real.exp (-t)) (Real.contDiff_exp.comp contDiff_neg) ph hph
  have h3 := SmoothR.mul n z _ _ (SmoothR.mul n z _ _ h1 h2) (smoothR_const n z (1 / r ^ 2))
  convert h3 using 1
  funext x
  simp [ev, div_eq_mul_inv]
end ReciprocityTheory.L2DbarEstimates.I
