-- Prove2me | solution 1 for PI.VolStabS.FiniteFieldCounting.inert_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:51:03.191422+00:00
-- url     : https://prove2.me/submissions/73e747bd-f38f-484c-83f7-ae92b96ee1d4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFT
import Theorems.Thm_PI_VolStabS_FiniteFieldCounting_inv_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open PI.VolStabS.FiniteFieldCounting
namespace PI.VolStabS.FiniteFieldCounting
theorem _root_.solution (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (j : Fin a) :
    |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| ≤ (q⁻¹) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hj := j.isLt
  rw [abs_neg, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (pow_pos hq0 _), abs_of_pos (pow_pos hq0 _)]
  have he : 2 * (M - (j : ℕ)) - 1 = (M - (j : ℕ) - 1) + (M - (j : ℕ)) := by omega
  rw [he, pow_add, div_mul_eq_div_div, div_self (pow_ne_zero _ hq0.ne'), one_div, ← inv_pow]
  exact inv_pow_le q hq _ (by omega)
end PI.VolStabS.FiniteFieldCounting
