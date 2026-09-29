-- Prove2me | solution 1 for ZMod.not_exists_sq_add_self_add_one_eq_zero_of_not_three_dvd_of_exists_prime_dvd_mod_three_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/f11b6b8d-01c4-5da2-863e-291113c2576c

import Mathlib
import Theorems.Thm_ZMod_prime_dvd_eq_three_or_mod_three_eq_one_of_sq_add_self_add_one_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ZMod_not_exists_sq_add_self_add_one_eq_zero_of_not_three_dvd_of_exists_prime_dvd_mod_three_ne_one

set_option autoImplicit false

theorem solution
    (M : ℕ) (hM : ¬ 3 ∣ M) (hℓ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 3 ≠ 1) :
    ¬ ∃ x : ZMod M, x ^ 2 + x + 1 = 0 := by
  rintro ⟨x, hx⟩
  obtain ⟨ℓ, hℓp, hℓM, hℓ3⟩ := hℓ
  rcases ZMod.prime_dvd_eq_three_or_mod_three_eq_one_of_sq_add_self_add_one_eq_zero x hx hℓp hℓM with h | h
  · subst h; exact hM hℓM
  · exact hℓ3 h

end S_ZMod_not_exists_sq_add_self_add_one_eq_zero_of_not_three_dvd_of_exists_prime_dvd_mod_three_ne_one
end P2MW
export P2MW.S_ZMod_not_exists_sq_add_self_add_one_eq_zero_of_not_three_dvd_of_exists_prime_dvd_mod_three_ne_one (solution)
