-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.sqBall_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:45.220194+00:00
-- url     : https://prove2.me/submissions/9be0870a-1042-4b64-8178-dfdbe6589df1

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
theorem _root_.solution (r : ℕ) (R : ℝ) : IsClosed (sqBall r E R) := by
  unfold sqBall
  exact isClosed_le (continuous_finset_sum _ fun k _ => (continuous_apply k).norm.pow 2)
    continuous_const
end ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
