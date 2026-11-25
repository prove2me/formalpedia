-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.tl_ev_smoothR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:26:32.406832+00:00
-- url     : https://prove2.me/submissions/87e172d2-1b5c-467e-af48-5ce4345bdc56

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA
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
noncomputable section
open Filter Topology
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r : ℝ) (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph) :
    SmoothR n z (ev n g ph r) := by
  have hS : SmoothR n z (fun x => ∑ i, ‖g i x‖ ^ 2) :=
    smoothR_sum n z Finset.univ _ fun i _ => Smooth.normSq n z _ (Holo.smooth n z _ (hg i))
  have hE : SmoothR n z (fun x => Real.exp (-ph x)) :=
    SmoothR.comp n z (fun t => Real.exp (-t)) (Real.contDiff_exp.comp contDiff_neg) ph hph
  exact SmoothR.comp n z (fun t => t / r ^ 2) (contDiff_id.div_const _) _ (SmoothR.mul n z _ _ hS hE)
end ReciprocityTheory.L2DbarEstimates.I
