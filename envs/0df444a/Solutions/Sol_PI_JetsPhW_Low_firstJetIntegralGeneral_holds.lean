-- Prove2me | solution 1 for PI.JetsPhW.Low.firstJetIntegralGeneral_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:54.925799+00:00
-- url     : https://prove2.me/submissions/e1ebf6d7-0173-4527-9977-67ea7a52705f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ExpLow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_FirstJetIntegralGeneralHolds
import Theorems.Thm_PI_JetsPhW_Low_logOk_low
import Theorems.Thm_PI_JetsPhW_Low_coeff_subst_of_degree_eq_one
import Theorems.Thm_PI_JetsPhW_Low_coeff_truncatedExp_of_degree_eq_one
import Theorems.Thm_PI_JetsPhW_Low_const_subst
import Theorems.Thm_PI_JetsPhW_Low_norm_two
import Theorems.Thm_PI_JetsPhW_Low_pcoeff1_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
open PI.JetsPhW
namespace PI.JetsPhW.Low
theorem _root_.solution : OneG := by
  intro p _ l ex ph h hp hs
  obtain ⟨_, _, h2⟩ := logOk_low h
  have h1 := (logOk_low h).2.1
  have h0 := (logOk_low h).1
  have hex := h.1
  have hde : Finsupp.degree (Finsupp.single () 1 : Unit →₀ ℕ) = 1 := by simp
  have hX0 : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := by simp [Xv]
  have hXe : MvPowerSeries.coeff (Finsupp.single () 1) (Xv () : MvPowerSeries Unit ℂ_[p]) = 1 := by
    simp [Xv, MvPowerSeries.coeff_X]
  have hL0 : MvPowerSeries.constantCoeff (PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = 0 := by
    rw [const_subst hX0]
    exact h0
  have hLe : MvPowerSeries.coeff (Finsupp.single () 1) (PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) =
      PowerSeries.coeff 1 l := by
    rw [coeff_subst_of_degree_eq_one hX0 l hde, hXe, mul_one]
  have hB0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.C (-1 : ℂ_[p]) * PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = 0 := by
    rw [map_mul, hL0, mul_zero]
  have hBe : MvPowerSeries.coeff (Finsupp.single () 1)
      (MvPowerSeries.C (-1 : ℂ_[p]) * PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = -PowerSeries.coeff 1 l := by
    rw [MvPowerSeries.coeff_C_mul, hLe, neg_one_mul]
  have hA0 : MvPowerSeries.constantCoeff (mulBy l ex (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 := by
    rw [mulBy, const_subst hB0]
    exact hex
  have hAe : MvPowerSeries.coeff (Finsupp.single () 1)
      (mulBy l ex (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = -1 := by
    rw [mulBy, coeff_subst_of_degree_eq_one hB0 ex hde, hBe]
    linear_combination (-1 : ℂ_[p]) * h1
  have hf : MvPowerSeries.coeff (Finsupp.single () 1)
      (phAt ph (mulBy l ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) = -PowerSeries.coeff 1 ph := by
    rw [phAt, coeff_subst_of_degree_eq_one hA0 ph hde, hAe, mul_neg_one]
  have hg : MvPowerSeries.coeff (Finsupp.single () 1) (phAt ph (Xv ()) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.coeff 1 ph := by
    rw [phAt, coeff_subst_of_degree_eq_one hX0 ph hde, hXe, mul_one]
  have hint := hs.2 (Finsupp.single () 1)
  unfold IsIntP at hint
  rw [coeff_truncatedExp_of_degree_eq_one _ hde, map_sub, hf, hg] at hint
  have hc : ‖PowerSeries.coeff 1 ph‖ ≤ 1 := by
    have h2c : -PowerSeries.coeff 1 ph - PowerSeries.coeff 1 ph = -(2 * PowerSeries.coeff 1 ph) := by
      ring
    rw [h2c, norm_neg, norm_mul, norm_two hp, one_mul] at hint
    exact hint
  show ‖((Nat.factorial 1 : ℕ) : ℂ_[p]) * PowerSeries.coeff 1 (PowerSeries.subst ex ph : PowerSeries ℂ_[p])‖ ≤ 1
  rw [pcoeff1_subst hex ph, Nat.factorial_one, Nat.cast_one, one_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) h2
end PI.JetsPhW.Low
