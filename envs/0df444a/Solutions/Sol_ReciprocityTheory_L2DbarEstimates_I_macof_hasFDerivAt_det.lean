-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.macof_hasFDerivAt_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:18:07.630528+00:00
-- url     : https://prove2.me/submissions/aeb326f4-3eae-4c1b-bb08-7b2282ea6a43

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_MacofFderivApplyContDiffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {n : ℕ} (B : V n → Matrix (Fin n) (Fin n) ℂ) (y : V n)
    (B' : Fin n → Fin n → (V n →L[ℝ] ℂ))
    (hB : ∀ i l, HasFDerivAt (fun w => B w i l) (B' i l) y) (v : V n) :
    fderiv ℝ (fun w => (B w).det) y v =
      ∑ i, ((B y).updateRow i (fun l => B' i l v)).det := by
  have hrows : HasFDerivAt (fun w => (fun i l => B w i l : Fin n → Fin n → ℂ))
      (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun l => B' i l) y :=
    hasFDerivAt_pi.2 fun i => hasFDerivAt_pi.2 fun l => hB i l
  have hcomp := ((macofDet n).hasFDerivAt (fun i l => B y i l)).comp y hrows
  have hc2 : HasFDerivAt (fun w => (B w).det)
      (((macofDet n).linearDeriv fun i l => B y i l).comp
        (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun l => B' i l)) y := hcomp
  rw [hc2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply,
    ContinuousLinearMap.pi_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl
end ReciprocityTheory.L2DbarEstimates.I
