-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.sqBall_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:11:31.867193+00:00
-- url     : https://prove2.me/submissions/ec14ed60-58bf-45ab-a942-c93c9e601fe1

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SquareNormBall_sqBall_subset

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
theorem _root_.solution (r : ℕ) (R : ℝ) : Bornology.IsBounded (sqBall r E R) := Metric.isBounded_closedBall.subset (sqBall_subset r R)
end ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
