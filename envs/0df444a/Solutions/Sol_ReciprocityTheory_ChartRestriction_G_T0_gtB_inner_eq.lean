-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.gtB_inner_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:19.855986+00:00
-- url     : https://prove2.me/submissions/a858e1ee-cea0-41bf-8cec-1d7259a2c0cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory Module Submodule
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = ∑ k, EuclideanSpace.equiv (Fin n) ℝ x k * EuclideanSpace.equiv (Fin n) ℝ y k := by
  first
    | simp [PiLp.inner_apply, mul_comm]
    | (rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct, mul_comm])
end ReciprocityTheory.ChartRestriction.G.T0
