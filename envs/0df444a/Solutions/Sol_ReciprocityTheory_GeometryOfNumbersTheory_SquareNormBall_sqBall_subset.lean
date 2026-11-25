-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.sqBall_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:00:58.515126+00:00
-- url     : https://prove2.me/submissions/6472d751-6d03-478a-af40-925a00c90172

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
theorem _root_.solution (r : ℕ) (R : ℝ) : sqBall r E R ⊆ Metric.closedBall 0 |R| := by
  intro u hu
  simp only [sqBall, Set.mem_setOf_eq] at hu
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg R)).2 fun k => ?_
  have hk : ‖u k‖ ^ 2 ≤ R ^ 2 :=
    (Finset.single_le_sum (f := fun k => ‖u k‖ ^ 2) (fun k _ => by positivity)
      (Finset.mem_univ k)).trans hu
  have := sq_le_sq.mp hk
  rwa [abs_of_nonneg (norm_nonneg _)] at this
end ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
