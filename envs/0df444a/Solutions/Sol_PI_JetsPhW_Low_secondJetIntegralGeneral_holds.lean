-- Prove2me | solution 1 for PI.JetsPhW.Low.secondJetIntegralGeneral_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:06:50.540737+00:00
-- url     : https://prove2.me/submissions/ca4c9ccc-5581-4890-aaf1-523150b1c663

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ExpLow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_FirstJetIntegralGeneralHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_SecondJetIntegralGeneralHolds
import Theorems.Thm_PI_JetsPhW_Low_coeff_expXY_mul
import Theorems.Thm_PI_JetsPhW_Low_coeff_expXY_subst
import Theorems.Thm_PI_JetsPhW_Low_coeff_expX_subst
import Theorems.Thm_PI_JetsPhW_Low_coeff_expY_subst
import Theorems.Thm_PI_JetsPhW_Low_const_subst
import Theorems.Thm_PI_JetsPhW_Low_degree_expXY
import Theorems.Thm_PI_JetsPhW_Low_expXY_ne_zero
import Theorems.Thm_PI_JetsPhW_Low_logOk_low
import Theorems.Thm_PI_JetsPhW_Low_pcoeff2_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.JetsPhW.Low
open PI.JetsPhW
private lemma coeff_mulBy_low_degree {p : ℕ} [Fact p.Prime] {l ex : PowerSeries ℂ_[p]} (hlog : LogOk l ex) (c : ℂ_[p])
    {A : MvPowerSeries (Fin 2) ℂ_[p]} (hA : MvPowerSeries.constantCoeff A = 0) :
    MvPowerSeries.constantCoeff (mulBy l ex c A) = 0 ∧
      MvPowerSeries.coeff E0 (mulBy l ex c A) = c * MvPowerSeries.coeff E0 A ∧
      MvPowerSeries.coeff E1 (mulBy l ex c A) = c * MvPowerSeries.coeff E1 A := by
  obtain ⟨hl0, hle, -⟩ := logOk_low hlog
  have hAl : MvPowerSeries.constantCoeff (PowerSeries.subst A l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [const_subst hA]; exact hl0
  have hI : MvPowerSeries.constantCoeff
      (MvPowerSeries.C c * PowerSeries.subst A l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_mul, hAl, mul_zero]
  have e : mulBy l ex c A = PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst A l) ex := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, const_subst hI]; exact hlog.1
  · rw [e, coeff_expX_subst hI, MvPowerSeries.coeff_C_mul, coeff_expX_subst hA]
    linear_combination (c * MvPowerSeries.coeff E0 A) * hle
  · rw [e, coeff_expY_subst hI, MvPowerSeries.coeff_C_mul, coeff_expY_subst hA]
    linear_combination (c * MvPowerSeries.coeff E1 A) * hle
private lemma coeff_be_low_degree {p : ℕ} [Fact p.Prime] {l ex : PowerSeries ℂ_[p]} (ph : PowerSeries ℂ_[p])
    (hlog : LogOk l ex) {A B : MvPowerSeries (Fin 2) ℂ_[p]} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (hA1 : MvPowerSeries.coeff E1 A = 0)
    (hB0 : MvPowerSeries.coeff E0 B = 0) :
    MvPowerSeries.coeff E0 (be l ex ph A B) = 0 ∧ MvPowerSeries.coeff E1 (be l ex ph A B) = 0 ∧
      MvPowerSeries.coeff bivariateExponentMonomial (be l ex ph A B) =
        2 * MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 B *
          (PowerSeries.coeff 1 ph * PowerSeries.coeff 2 ex * PowerSeries.coeff 1 l ^ 2 +
            PowerSeries.coeff 2 ph) := by
  obtain ⟨hl0, hle, -⟩ := logOk_low hlog
  have hAl : MvPowerSeries.constantCoeff (PowerSeries.subst A l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [const_subst hA]; exact hl0
  have hBl : MvPowerSeries.constantCoeff (PowerSeries.subst B l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [const_subst hB]; exact hl0
  have hS : MvPowerSeries.constantCoeff
      (PowerSeries.subst A l + PowerSeries.subst B l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_add, hAl, hBl, add_zero]
  have ea : add l ex A B = PowerSeries.subst (PowerSeries.subst A l + PowerSeries.subst B l) ex := rfl
  have hadd : MvPowerSeries.constantCoeff (add l ex A B) = 0 := by
    rw [ea, const_subst hS]; exact hlog.1
  have eb : be l ex ph A B = PowerSeries.subst (add l ex A B) ph - PowerSeries.subst A ph -
      PowerSeries.subst B ph := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [eb, map_sub, map_sub, coeff_expX_subst hadd, coeff_expX_subst hA, coeff_expX_subst hB, ea, coeff_expX_subst hS, map_add,
      coeff_expX_subst hA, coeff_expX_subst hB, hB0]
    linear_combination (PowerSeries.coeff 1 ph * MvPowerSeries.coeff E0 A) * hle
  · rw [eb, map_sub, map_sub, coeff_expY_subst hadd, coeff_expY_subst hA, coeff_expY_subst hB, ea, coeff_expY_subst hS, map_add,
      coeff_expY_subst hA, coeff_expY_subst hB, hA1]
    linear_combination (PowerSeries.coeff 1 ph * MvPowerSeries.coeff E1 B) * hle
  · rw [eb, map_sub, map_sub, coeff_expXY_subst hadd, coeff_expXY_subst hA, coeff_expXY_subst hB,
      ea, coeff_expXY_subst hS, coeff_expX_subst hS, coeff_expY_subst hS, map_add, map_add, map_add, coeff_expXY_subst hA, coeff_expXY_subst hB,
      coeff_expX_subst hA, coeff_expX_subst hB, coeff_expY_subst hA, coeff_expY_subst hB, hA1, hB0]
    linear_combination (PowerSeries.coeff 1 ph * (MvPowerSeries.coeff bivariateExponentMonomial A + MvPowerSeries.coeff bivariateExponentMonomial B) +
      2 * MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 B * PowerSeries.coeff 2 ph *
        (PowerSeries.coeff 1 ex * PowerSeries.coeff 1 l + 1)) * hle
end PI.JetsPhW.Low
end
end

set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
open PI.JetsPhW
namespace PI.JetsPhW.Low
theorem _root_.solution : TwoG := by
  intro p _ l ex ph a b hlog hsim
  obtain ⟨hl0, hle, he1⟩ := logOk_low hlog
  have hex0 : PowerSeries.constantCoeff ex = 0 := hlog.1
  have cX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := fun i => by
    simp [Xv]
  have x00 : MvPowerSeries.coeff E0 (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 1 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  have x01 : MvPowerSeries.coeff E1 (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  have x10 : MvPowerSeries.coeff E0 (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  have x11 : MvPowerSeries.coeff E1 (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 1 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  obtain ⟨ma0, ma1, ma2⟩ := coeff_mulBy_low_degree hlog a (cX 0)
  obtain ⟨mb0, mb1, mb2⟩ := coeff_mulBy_low_degree hlog b (cX 1)
  obtain ⟨u0, u1, u2⟩ := coeff_be_low_degree ph hlog ma0 (cX 1) (by rw [ma2, x01, mul_zero]) x10
  obtain ⟨v0, v1, v2⟩ := coeff_be_low_degree ph hlog (cX 0) mb0 x01 (by rw [mb1, x10, mul_zero])
  set D := (be l ex ph (mulBy l ex a (Xv 0)) (Xv 1) - be l ex ph (Xv 0) (mulBy l ex b (Xv 1)) :
    MvPowerSeries (Fin 2) ℂ_[p]) with hD
  have hD0 : MvPowerSeries.constantCoeff D = 0 := hsim.1
  have d0 : MvPowerSeries.coeff E0 D = 0 := by rw [hD, map_sub, u0, v0, sub_zero]
  have d1 : MvPowerSeries.coeff E1 D = 0 := by rw [hD, map_sub, u1, v1, sub_zero]

  have hs : (bivariateExponentMonomial.sum fun _ k => k) = 2 := degree_expXY
  have hexp : MvPowerSeries.coeff bivariateExponentMonomial (expMv D) = MvPowerSeries.coeff bivariateExponentMonomial D := by
    change (∑ n ∈ Finset.range ((bivariateExponentMonomial.sum fun _ k => k) + 1),
      MvPowerSeries.coeff bivariateExponentMonomial (D ^ n) / (n.factorial : ℂ_[p])) = _
    rw [hs, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, pow_two,
      coeff_expXY_mul hD0 hD0, d0, d1]
    simp [MvPowerSeries.coeff_one, expXY_ne_zero]
  have hint : ‖MvPowerSeries.coeff bivariateExponentMonomial D‖ ≤ 1 := by
    rw [← hexp]; exact hsim.2 bivariateExponentMonomial
  have hjet : jet ex ph 2 = 2 * (PowerSeries.coeff 1 ph * PowerSeries.coeff 2 ex +
      PowerSeries.coeff 2 ph * PowerSeries.coeff 1 ex ^ 2) := by
    unfold jet
    rw [pcoeff2_subst hex0 ph]
    norm_num
  have hval : MvPowerSeries.coeff bivariateExponentMonomial D = (a - b) * jet ex ph 2 * PowerSeries.coeff 1 l ^ 2 := by
    rw [hD, map_sub, u2, v2, ma1, mb2, x00, x11, hjet]
    linear_combination (-2 * (a - b) * PowerSeries.coeff 2 ph *
      (PowerSeries.coeff 1 ex * PowerSeries.coeff 1 l + 1)) * hle

  have hl1 : 1 ≤ ‖PowerSeries.coeff 1 l‖ := by
    have h := congrArg norm hle
    rw [norm_mul, norm_one] at h
    by_contra hlt
    push_neg at hlt
    nlinarith [norm_nonneg (PowerSeries.coeff 1 ex), norm_nonneg (PowerSeries.coeff 1 l)]
  rw [hval, norm_mul, norm_pow] at hint
  unfold IsIntP
  have hxy := norm_nonneg ((a - b) * jet ex ph 2)
  have := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) hl1) hxy
  linarith
end PI.JetsPhW.Low
