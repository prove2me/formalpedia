-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.moll_le_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:15:07.136411+00:00
-- url     : https://prove2.me/submissions/3273f8db-1ae7-412f-b221-2325b5803ea2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollLeClosedBall
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_le


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
theorem _root_.solution (n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ x z : V n,
      moll n t z ≤ C / volume.real (closedBall x t) := by
  obtain ⟨C, hC⟩ := moll_le n
  refine ⟨C, fun t ht x z => ?_⟩
  have hvol : volume.real (closedBall x t) = volume.real (ball (0 : V n) t) := by
    rcases subsingleton_or_nontrivial (V n) with hV | hV
    · have h1 : closedBall x t = univ := eq_univ_of_forall fun y => by
        rw [Subsingleton.elim y x]; exact mem_closedBall_self ht.le
      have h2 : ball (0 : V n) t = univ := eq_univ_of_forall fun y => by
        rw [Subsingleton.elim y 0]; exact mem_ball_self ht
      rw [h1, h2]
    · simp only [measureReal_def]
      rw [Measure.addHaar_closedBall_eq_addHaar_ball, Measure.addHaar_ball_center]
  rw [hvol]
  exact hC t ht z
end ReciprocityTheory.L2DbarEstimates.C
