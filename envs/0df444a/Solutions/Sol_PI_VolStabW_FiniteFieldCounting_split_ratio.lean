-- Prove2me | solution 1 for PI.VolStabW.FiniteFieldCounting.split_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:16.361898+00:00
-- url     : https://prove2.me/submissions/9ed7f79c-9dca-479f-a3d6-e10ddedb6826

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFT
import Theorems.Thm_PI_VolStabW_FiniteFieldCounting_exp_id

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
    (∏ i : Fin a, (q ^ M - q ^ (i : ℕ))) * q ^ (a * (M - a)) / q ^ (2 * M * a - a ^ 2) =
      ∏ i : Fin a, (1 + -(q ^ (i : ℕ) / q ^ M)) := by
  have hM : q ^ M ≠ 0 := pow_ne_zero _ hq
  have e1 : ∀ i : Fin a, q ^ M - q ^ (i : ℕ) = q ^ M * (1 + -(q ^ (i : ℕ) / q ^ M)) := by
    intro i
    field_simp
    ring
  rw [Finset.prod_congr rfl fun i _ ↦ e1 i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul, ← exp_id M a ha, pow_add]
  have h1 : q ^ (M * a) ≠ 0 := pow_ne_zero _ hq
  have h2 : q ^ (a * (M - a)) ≠ 0 := pow_ne_zero _ hq
  field_simp
end PI.VolStabW.FiniteFieldCounting
