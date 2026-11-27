-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flA_leviV_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:31:52.725398+00:00
-- url     : https://prove2.me/submissions/188df46e-c60a-4bc7-96ab-3990ed533517

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_wdb
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_eventually_differentiableAt_of_contDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {F G : V n → ℝ} {y : V n} (hF : ContDiffAt ℝ 2 F y)
    (hG : ContDiffAt ℝ 2 G y) (ξ : Fin n → ℂ) :
    leviV n (fun v => ((F v + G v : ℝ) : ℂ)) y ξ =
      leviV n (fun v => (F v : ℂ)) y ξ + leviV n (fun v => (G v : ℂ)) y ξ := by
  have hFc : ContDiffAt ℝ 2 (fun v => (F v : ℂ)) y := ofRealCLM.contDiff.contDiffAt.comp y hF
  have hGc : ContDiffAt ℝ 2 (fun v => (G v : ℂ)) y := ofRealCLM.contDiff.contDiffAt.comp y hG
  have hfun : (fun v => ((F v + G v : ℝ) : ℂ)) = fun v => (F v : ℂ) + (G v : ℂ) := by
    funext v; push_cast; rfl
  have hev : ∀ k, wdb n k (fun v => (F v : ℂ) + (G v : ℂ)) =ᶠ[𝓝 y]
      fun v => wdb n k (fun v => (F v : ℂ)) v + wdb n k (fun v => (G v : ℂ)) v := by
    intro k
    filter_upwards [eventually_differentiableAt_of_contDiffAt hFc,
      eventually_differentiableAt_of_contDiffAt hGc] with v h1 h2
    exact wdb_add h1 h2
  rw [hfun]
  simp only [leviV]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [wd_congr (hev k), wd_add (differentiableAt_wdb hFc) (differentiableAt_wdb hGc)]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
