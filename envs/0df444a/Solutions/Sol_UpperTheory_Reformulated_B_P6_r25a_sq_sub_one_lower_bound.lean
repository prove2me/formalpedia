-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r25a.sq_sub_one_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:49:02.652035+00:00
-- url     : https://prove2.me/submissions/8c73373d-0940-4eaf-9ee9-56812c0027f5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_PowTwoPowSubOneGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r25a
namespace UpperTheory.Reformulated.B.P6.r25a
theorem _root_.solution (w : ℂ) (hw : ‖w - 1‖ < 1 / 2) :
    (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have h1 : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
  have h2 : (w + 1) - (w - 1) = (2 : ℂ) := by ring
  have h3 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have h := norm_sub_le (w + 1) (w - 1)
    rwa [h2] at h
  have h4 : ‖(2 : ℂ)‖ = 2 := by simp
  have h5 : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by linarith
  have h6 : 0 ≤ ‖w - 1‖ := norm_nonneg _
  have h7 : ‖w - 1‖ * (3 / 2) ≤ ‖w - 1‖ * ‖w + 1‖ := mul_le_mul_of_nonneg_left h5 h6
  rw [h1, norm_mul]
  linarith
end UpperTheory.Reformulated.B.P6.r25a
