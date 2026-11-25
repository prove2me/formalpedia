-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.isTest_moll_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:22.405999+00:00
-- url     : https://prove2.me/submissions/3b5f61af-1843-4764-96c4-d71695799257

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_sub_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_contDiff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} {Ω : Set (V n)} {t : ℝ} {x : V n} (ht : 0 < t)
    (hx : closedBall x t ⊆ Ω) : IsTest Ω (fun y => ((moll n t (x - y) : ℝ) : ℂ)) := by
  have hz : ∀ y ∉ closedBall x (t / 2), ((moll n t (x - y) : ℝ) : ℂ) = 0 := fun y hy => by
    rw [moll_sub_eq_zero ht hy, Complex.ofReal_zero]
  refine ⟨?_, HasCompactSupport.intro (isCompact_closedBall x (t / 2)) hz, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((moll_contDiff n t).comp (contDiff_const.sub contDiff_id))
  · exact (closure_minimal (Function.support_subset_iff'.2 hz) isClosed_closedBall).trans
      ((closedBall_subset_closedBall (by linarith)).trans hx)
end ReciprocityTheory.L2DbarEstimates.C
