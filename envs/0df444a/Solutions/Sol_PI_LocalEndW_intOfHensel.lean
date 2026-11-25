-- Prove2me | solution 1 for PI.LocalEndW.intOfHensel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:03:40.137217+00:00
-- url     : https://prove2.me/submissions/631c61fe-479d-4cce-ab41-c1f2a44457e4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocalEnd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IntVal
import Theorems.Thm_PI_LocalEndW_exists_N
import Theorems.Thm_PI_LocalEndW_le_one_of_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WithZero
open PI PI.LocalEndW
namespace PI.LocalEndW
theorem _root_.solution : IntOfHensel := by
  intro hH F _ _ v τ x hx
  obtain ⟨N, hNpos, m, hm, hNv, hℓ⟩ := exists_N v
  obtain ⟨ℓ, hge, hprime⟩ := Nat.exists_infinite_primes (N + m + 1)
  have hℓ1 := hℓ ℓ hprime (by omega)
  have hu : Valued.v ((1 + (N : v.adicCompletion F) * x ^ ℓ) - 1) < 1 := by
    rw [add_sub_cancel_left, map_mul, map_pow, hNv]
    calc exp (-(m : ℤ)) * Valued.v x ^ ℓ ≤ exp (-(m : ℤ)) * 1 :=
          by gcongr; exact pow_le_one₀ zero_le hx
      _ < 1 := by rw [mul_one, ← exp_zero, exp_lt_exp]; omega
  obtain ⟨z, hz⟩ := hH F v ℓ _ hℓ1 hu
  have hτ : (τ z) ^ ℓ = 1 + (N : v.adicCompletion F) * (τ x) ^ ℓ := by
    rw [← map_pow, hz, map_add, map_one, map_mul, map_natCast, map_pow]
  exact le_one_of_pow_eq v hm (by omega) hNv hτ
end PI.LocalEndW
