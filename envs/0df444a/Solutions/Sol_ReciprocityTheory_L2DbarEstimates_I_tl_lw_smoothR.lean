-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.tl_lw_smoothR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:37:37.672241+00:00
-- url     : https://prove2.me/submissions/19fa96ad-35c2-4501-b95f-00a5561b7202

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tlFlr_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tlFlr_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tlFlr_ge
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_ev_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_ev_smoothR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_smoothR_const


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
    (ph : M → ℝ) (r δ : ℝ) (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph) (hδ : 0 < δ) :
    SmoothR n z (lw n g ph r δ) := by
  have hd : 0 < δ ^ 2 := by positivity
  have hL : ContDiff ℝ ∞ (fun t => Real.log (tlFlr (δ ^ 2) (δ ^ 2 / 2) t)) :=
    (tlFlr_contDiff _ _).log fun t => by
      have := tlFlr_ge (δ ^ 2) (δ ^ 2 / 2) t (by linarith)
      exact (show 0 < tlFlr (δ ^ 2) (δ ^ 2 / 2) t by linarith).ne'
  have h := SmoothR.comp n z _ hL (fun x => ev n g ph r x + δ ^ 2)
    (SmoothR.add n z _ _ (tl_ev_smoothR n z g ph r hg hph) (smoothR_const n z _))
  have heq : (fun x => Real.log (tlFlr (δ ^ 2) (δ ^ 2 / 2) (ev n g ph r x + δ ^ 2))) = lw n g ph r δ := by
    funext x
    unfold lw
    rw [tlFlr_eq _ _ _ (by linarith) (by linarith [tl_ev_nonneg n g ph r x])]
  rw [heq] at h
  exact h
end ReciprocityTheory.L2DbarEstimates.I
