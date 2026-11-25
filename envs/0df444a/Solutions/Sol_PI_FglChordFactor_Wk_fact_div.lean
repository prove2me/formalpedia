-- Prove2me | solution 1 for PI.FglChordFactor.Wk.fact_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:53:31.076674+00:00
-- url     : https://prove2.me/submissions/7488b1da-a175-47e5-8e4f-77d01c8751ec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstPairSecondVariable
import Theorems.Thm_PI_FglChordFactor_Wk_hasSubst2
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_first_variable
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_second_variable
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_first_series
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_comp
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_variables_self
import Theorems.Thm_PI_FglChordFactor_Wk_X_mem_SerS
import Theorems.Thm_PI_FglChordFactor_Wk_serS_unit
import Theorems.Thm_PI_FglChordFactor_Wk_coeff_mul_second_variable
import Theorems.Thm_PI_FglChordFactor_Wk_single0_iff
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_psubst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.FglChordFactor PI.FglChordFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS subst_mem_SerS subst_psubst)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglChordFactor.Wk
theorem _root_.solution {S : Subring ℂ_[p]} {H : MvPowerSeries (Fin 2) ℂ_[p]} {f : PowerSeries ℂ_[p]}
    (hf0 : PowerSeries.constantCoeff f = 0) (hfS : ∀ n, PowerSeries.coeff n f ∈ S) (hH : H ∈ SerS S (Fin 2))
    (hz : MvPowerSeries.subst ![MvPowerSeries.X 0,
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) f] H = 0) :
    ∃ Q ∈ SerS S (Fin 2),
      H = (MvPowerSeries.X 1 - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) f) * Q := by
  set a : MvPowerSeries (Fin 2) ℂ_[p] := MvPowerSeries.X 0 with ha
  set b : MvPowerSeries (Fin 2) ℂ_[p] := MvPowerSeries.X 1 with hb
  set s : MvPowerSeries (Fin 2) ℂ_[p] := PowerSeries.subst a f with hs
  have ha0 : MvPowerSeries.constantCoeff a = 0 := MvPowerSeries.constantCoeff_X 0
  have hb0 : MvPowerSeries.constantCoeff b = 0 := MvPowerSeries.constantCoeff_X 1
  have hs0 : MvPowerSeries.constantCoeff s = 0 := PowerSeries.constantCoeff_subst_eq_zero ha0 f hf0
  have haS : a ∈ SerS S (Fin 2) := X_mem_SerS S 0
  have hbS : b ∈ SerS S (Fin 2) := X_mem_SerS S 1
  have hsS : s ∈ SerS S (Fin 2) := subst_mem_SerS S ha0 haS (serS_unit hfS)
  have hP : MvPowerSeries.HasSubst ![a, b + s] := hasSubst2 ha0 (by rw [map_add, hb0, hs0, add_zero])
  have hM : MvPowerSeries.HasSubst ![a, b - s] := hasSubst2 ha0 (by rw [map_sub, hb0, hs0, sub_zero])
  have hZ : MvPowerSeries.HasSubst ![a, (0 : MvPowerSeries (Fin 2) ℂ_[p])] := hasSubst2 ha0 (map_zero _)
  set Hp := MvPowerSeries.subst ![a, b + s] H with hHp

  have hback : MvPowerSeries.subst ![a, b - s] Hp = H := by
    rw [hHp, subst_pair_comp hM hP, subst_pair_first_variable hM, MvPowerSeries.subst_add hM, subst_pair_second_variable hM, hs, subst_pair_first_series hM, ← hs,
      sub_add_cancel, ha, hb, subst_pair_variables_self]

  have hzero : MvPowerSeries.subst ![a, (0 : MvPowerSeries (Fin 2) ℂ_[p])] Hp = 0 := by
    rw [hHp, subst_pair_comp hZ hP, subst_pair_first_variable hZ, MvPowerSeries.subst_add hZ, subst_pair_second_variable hZ, hs, subst_pair_first_series hZ, ← hs,
      zero_add]
    exact hz

  set Qt : MvPowerSeries (Fin 2) ℂ_[p] := fun e => MvPowerSeries.coeff (e + Finsupp.single 1 1) Hp with hQt
  set r : PowerSeries ℂ_[p] := PowerSeries.mk fun n => MvPowerSeries.coeff (Finsupp.single 0 n) Hp with hr
  have hdec : Hp = Qt * b + PowerSeries.subst a r := by
    ext e
    rw [map_add, hb, coeff_mul_second_variable, ha, PowerSeries.coeff_subst_single]
    by_cases he : e 1 = 0
    · have he' : e = Finsupp.single 0 (e 0) := (single0_iff e).2 he
      rw [if_neg (by omega), if_pos he', zero_add, hr, PowerSeries.coeff_mk, ← he']
    · have he' : ¬ e = Finsupp.single 0 (e 0) := fun h => he ((single0_iff e).1 h)
      rw [if_pos (by omega), if_neg he', add_zero]
      show MvPowerSeries.coeff e Hp = MvPowerSeries.coeff (e - Finsupp.single 1 1 + Finsupp.single 1 1) Hp
      rw [tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by omega))]
  have hR : PowerSeries.subst a r = 0 := by
    have h1 := hzero
    rw [hdec, MvPowerSeries.subst_add hZ, MvPowerSeries.subst_mul hZ, subst_pair_second_variable hZ, mul_zero, zero_add, ha,
      subst_pair_first_series hZ] at h1
    exact h1
  have hdec' : Hp = Qt * b := by rw [hdec, hR, add_zero]
  have hQtS : Qt ∈ SerS S (Fin 2) := by
    have hHpS : Hp ∈ SerS S (Fin 2) :=
      mvsubst_mem_SerS S (Fin.forall_fin_two.2 ⟨by simpa using ha0, by simp [hb0, hs0]⟩)
        (Fin.forall_fin_two.2 ⟨by simpa using haS, by simpa using add_mem hbS hsS⟩) hH
    rw [mem_SerS]; intro e
    exact (mem_SerS S Hp).1 hHpS _
  refine ⟨MvPowerSeries.subst ![a, b - s] Qt, ?_, ?_⟩
  · exact mvsubst_mem_SerS S (Fin.forall_fin_two.2 ⟨by simpa using ha0, by simp [hb0, hs0]⟩)
      (Fin.forall_fin_two.2 ⟨by simpa using haS, by simpa using sub_mem hbS hsS⟩) hQtS
  · conv_lhs => rw [← hback, hdec', MvPowerSeries.subst_mul hM, hb, subst_pair_second_variable hM]
    ring
end PI.FglChordFactor.Wk
