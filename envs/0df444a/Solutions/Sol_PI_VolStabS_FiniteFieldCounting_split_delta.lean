-- Prove2me | solution 1 for PI.VolStabS.FiniteFieldCounting.split_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:50:19.647247+00:00
-- url     : https://prove2.me/submissions/93615ac4-2fea-4e59-a89b-e5528708d822

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
theorem _root_.solution (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (i : Fin a) :
    |-(q ^ (i : ℕ) / q ^ M)| ≤ (q⁻¹) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hi := i.isLt
  rw [abs_neg, abs_of_nonneg (div_nonneg (pow_nonneg hq0.le _) (pow_nonneg hq0.le _))]
  have hM : M = (i : ℕ) + (M - i) := by omega
  have h1 : q ^ (i : ℕ) / q ^ M = (q⁻¹) ^ (M - i) := by
    conv_lhs => rw [hM, pow_add]
    rw [div_mul_eq_div_div, div_self (pow_ne_zero _ hq0.ne'), inv_pow, one_div]
  rw [h1]
  exact inv_pow_le q hq (M - i) (by omega)
end PI.VolStabS.FiniteFieldCounting
