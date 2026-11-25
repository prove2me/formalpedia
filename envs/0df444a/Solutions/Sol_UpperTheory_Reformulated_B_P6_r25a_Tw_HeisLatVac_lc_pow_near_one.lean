-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r25a.Tw.HeisLatVac.lc_pow_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:27:14.642349+00:00
-- url     : https://prove2.me/submissions/8a1027af-15fc-4a45-a159-d0636eb9ce3a

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_PowTwoPowSubOneGrowth
import Theorems.Thm_UpperTheory_Reformulated_B_P6_r25a_pow_two_pow_sub_one_growth

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
namespace Tw.HeisLatVac
theorem _root_.solution :
    ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - OfNat.ofNat (nat_lit 1)‖ < OfNat.ofNat (nat_lit 1) / OfNat.ofNat (nat_lit 2)) → z = OfNat.ofNat (nat_lit 1) := by
  intro z hz
  have hz' : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2 := hz
  have hstep := pow_two_pow_sub_one_growth z hz'
  have hd : ‖z - 1‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖z - 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
    have h1 := hstep k
    have h2 := hz' (2 ^ k)
    have h2d : (0 : ℝ) < 2 * ‖z - 1‖ := by positivity
    rw [div_lt_iff₀ h2d] at hk
    have h3 : (3 / 2 : ℝ) ^ k * (2 * ‖z - 1‖) = 2 * ((3 / 2) ^ k * ‖z - 1‖) := by ring
    linarith
  have hz1 : z - 1 = 0 := norm_eq_zero.mp hd
  exact sub_eq_zero.mp hz1
end Tw.HeisLatVac
end UpperTheory.Reformulated.B.P6.r25a
