-- Prove2me | solution 1 for PI.VolStabS.FiniteFieldCounting.split_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:20.340049+00:00
-- url     : https://prove2.me/submissions/fd3e4651-f6b4-449f-b3ce-bc6c874fdecc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFT
import Theorems.Thm_PI_VolStabS_FiniteFieldCounting_exp_id

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
theorem _root_.solution (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ i : Fin a, (q ^ M - q ^ (i : ℕ))) * q ^ (a * (M - a)) / q ^ (2 * M * a - a ^ 2) =
      ∏ i : Fin a, (1 + -(q ^ (i : ℕ) / q ^ M)) := by
  have hqM : q ^ M ≠ 0 := pow_ne_zero _ hq
  rw [← exp_id M a ha, pow_add]
  have h1 : ∀ i : Fin a, q ^ M - q ^ (i : ℕ) = q ^ M * (1 + -(q ^ (i : ℕ) / q ^ M)) := by
    intro i
    field_simp
    ring
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hA : q ^ (M * a) ≠ 0 := pow_ne_zero _ hq
  have hB : q ^ (a * (M - a)) ≠ 0 := pow_ne_zero _ hq
  rw [mul_comm (q ^ (M * a)), mul_assoc, mul_div_assoc, div_self (mul_ne_zero hA hB), mul_one]
end PI.VolStabS.FiniteFieldCounting
