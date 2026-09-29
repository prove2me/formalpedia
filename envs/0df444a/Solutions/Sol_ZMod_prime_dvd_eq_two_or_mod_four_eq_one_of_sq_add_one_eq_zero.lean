-- Prove2me | solution 1 for ZMod.prime_dvd_eq_two_or_mod_four_eq_one_of_sq_add_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/cc8e3931-29e6-5d00-a3f1-30f610b19462

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ZMod_prime_dvd_eq_two_or_mod_four_eq_one_of_sq_add_one_eq_zero

set_option autoImplicit false

theorem solution
    {M : ℕ} (x : ZMod M) (hx : x ^ 2 + 1 = 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) :
    ℓ = 2 ∨ ℓ % 4 = 1 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  set y : ZMod ℓ := ZMod.castHom hℓM (ZMod ℓ) x with hy
  have hy0 : y ^ 2 + 1 = 0 := by
    have := congrArg (ZMod.castHom hℓM (ZMod ℓ)) hx
    rw [map_add, map_pow, map_one, map_zero] at this
    exact this
  have hsq : IsSquare (-1 : ZMod ℓ) := ⟨y, by rw [← sq]; linear_combination -hy0⟩
  have h4 : ℓ % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp hsq
  rcases hℓ.eq_two_or_odd' with h2 | hodd
  · exact Or.inl h2
  · right
    obtain ⟨k, hk⟩ := hodd
    omega

end S_ZMod_prime_dvd_eq_two_or_mod_four_eq_one_of_sq_add_one_eq_zero
end P2MW
export P2MW.S_ZMod_prime_dvd_eq_two_or_mod_four_eq_one_of_sq_add_one_eq_zero (solution)
