-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flL_det_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:21:26.909841+00:00
-- url     : https://prove2.me/submissions/9fcc1e3b-4688-469e-9474-2895ccddedba

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_det_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {G : V n → V n →L[ℂ] V n} {y : V n} (hG : ContDiffAt ℂ ∞ G y) :
    ContDiffAt ℂ ∞ (fun v => (G v).det) y := by

  have e : (fun v => (G v).det) = fun v => ∑ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ : ℂ) * ∏ c, G v (bas n c) (σ c) := funext fun v => flL_det_eq (G v)
  rw [e]
  refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun c _ => ?_)
  exact ((EuclideanSpace.proj (σ c)).comp
    (ContinuousLinearMap.apply ℂ (V n) (bas n c))).contDiff.contDiffAt.comp y hG
end ReciprocityTheory.L2DbarEstimates.Y
