-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_measurable_gt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:40:04.336828+00:00
-- url     : https://prove2.me/submissions/e5c912af-2f8f-4965-85ea-f204df4cfd28

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_gt_eq_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_holo_jac
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


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
open scoped ENNReal ContDiff Classical
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
    (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ)
    (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ)
    (hS : (zeroSet n g).Finite) (hW : IsLocalData n g ph r W m) :
    Measurable (gt n z g c W) := by
  have hJ : Continuous (jac n z g) :=
    Smooth.continuous n z hz _ (Holo.smooth n z _ (ap_holo_jac n z g hg))
  have h : gt n z g c W = fun y => ∑ p ∈ hS.toFinset, (W p).indicator (fun y => c p * jac n z g y) y :=
    funext (ap_gt_eq_sum n z g c W hS)
  rw [h]
  apply Finset.measurable_sum
  intro p hp
  exact (measurable_const.mul hJ.measurable).indicator
    (hW.2 p (hS.mem_toFinset.1 hp)).1.measurableSet
end ReciprocityTheory.L2DbarEstimates.I
