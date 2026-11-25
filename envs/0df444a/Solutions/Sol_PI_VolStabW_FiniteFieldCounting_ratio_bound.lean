-- Prove2me | solution 1 for PI.VolStabW.FiniteFieldCounting.ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:47.575942+00:00
-- url     : https://prove2.me/submissions/29238380-586d-40e9-a8c4-c57844abbf59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFT
import Theorems.Thm_PI_VolStabW_FiniteFieldCounting_prod_bound

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
theorem _root_.solution (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : 1 ≤ q) (δ : Fin a → ℝ)
    (h : ∀ j, |δ j| ≤ (q⁻¹) ^ 2) : |∏ j, (1 + δ j) - 1| ≤ 2 ^ M * (q⁻¹) ^ 2 := by
  have ht0 : 0 ≤ (q⁻¹) ^ 2 := by positivity
  have ht1 : (q⁻¹) ^ 2 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq)
  have := prod_bound δ _ ht0 ht1 h Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at this
  have h2 : (2 : ℝ) ^ a ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) ha
  nlinarith
end PI.VolStabW.FiniteFieldCounting
