-- Prove2me | solution 1 for PI.VolStabW.FiniteFieldCounting.inert_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:05:54.198734+00:00
-- url     : https://prove2.me/submissions/252d9a24-6b22-4047-b89d-b4675778a5b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFT
import Theorems.Thm_PI_VolStabW_FiniteFieldCounting_sum_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.FiniteFieldCounting
namespace PI.VolStabW.FiniteFieldCounting
theorem _root_.solution (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ j : Fin a, (q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1))) /
        q ^ (2 * M * a - a ^ 2) =
      ∏ j : Fin a, (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
  have e1 : ∀ j : Fin a, q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1) =
      q ^ (2 * (M - j) - 1) *
        (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
    intro j
    have : q ^ (2 * (M - j) - 1) ≠ 0 := pow_ne_zero _ hq
    field_simp
    ring
  rw [Finset.prod_congr rfl fun j _ ↦ e1 j, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun j ↦ 2 * (M - j) - 1) a, sum_exp M a ha]
  have h1 : q ^ (2 * M * a - a ^ 2) ≠ 0 := pow_ne_zero _ hq
  field_simp
end PI.VolStabW.FiniteFieldCounting
