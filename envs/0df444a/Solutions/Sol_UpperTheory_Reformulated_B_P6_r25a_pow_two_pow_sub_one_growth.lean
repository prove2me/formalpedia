-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r25a.pow_two_pow_sub_one_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:12:19.437362+00:00
-- url     : https://prove2.me/submissions/779ee5fa-9827-46fb-b9eb-270cb452caba

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_PowTwoPowSubOneGrowth
import Theorems.Thm_UpperTheory_Reformulated_B_P6_r25a_sq_sub_one_lower_bound

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
theorem _root_.solution (z : ℂ) (hz : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) :
    ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by
      rw [← pow_mul, ← pow_succ]
    have hs := sq_sub_one_lower_bound (z ^ (2 ^ k)) (hz _)
    calc (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = (3 / 2) * ((3 / 2) ^ k * ‖z - 1‖) := by ring
      _ ≤ (3 / 2) * ‖z ^ (2 ^ k) - 1‖ := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ ‖(z ^ (2 ^ k)) ^ 2 - 1‖ := hs
      _ = ‖z ^ (2 ^ (k + 1)) - 1‖ := by rw [e]
end UpperTheory.Reformulated.B.P6.r25a
