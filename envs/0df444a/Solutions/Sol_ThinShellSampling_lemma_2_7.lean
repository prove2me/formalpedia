-- Prove2me | solution 1 for ThinShellSampling.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:14:38.711384+00:00
-- url     : https://prove2.me/submissions/ea037beb-aee4-4bcd-87d6-b41a2f2e16e4

import Mathlib
import Definitions.Def_ThinShellSampling_renyi

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem solution {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → β) (hX : Measurable X) (S : Set Ω) (hS : MeasurableSet S)
    (η : ℝ) (hη : η < 1) (hPS : ENNReal.ofReal (1 - η) ≤ P S) (πX : Measure β)
    [IsProbabilityMeasure πX] :
    (ProbabilityTheory.cond P S).map X ≤ ENNReal.ofReal (1 / (1 - η)) • P.map X ∧
    ThinShellSampling.renyiInf ((ProbabilityTheory.cond P S).map X) (P.map X) ≤
      ENNReal.ofReal (Real.log (1 / (1 - η))) ∧
    ∀ q : ℝ, 1 < q →
      ThinShellSampling.renyi q ((ProbabilityTheory.cond P S).map X) πX ≤
        ThinShellSampling.renyi q (P.map X) πX +
          ENNReal.ofReal (q / (q - 1) * Real.log (1 / (1 - η))) := by
  have h1η : 0 < 1 - η := by linarith
  have hη0 : 0 ≤ η := by
    have h := hPS.trans (prob_le_one (μ := P) (s := S))
    rw [ENNReal.ofReal_le_one] at h
    linarith
  have hcge : 1 ≤ 1 / (1 - η) := by rw [le_div_iff₀ h1η]; linarith
  have hcpos : 0 < 1 / (1 - η) := by positivity
  have hS0 : P S ≠ 0 := by
    intro h
    rw [h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hPS
    linarith
  haveI : IsProbabilityMeasure (cond P S) := cond_isProbabilityMeasure hS0
  haveI : IsProbabilityMeasure ((cond P S).map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - η)) with hc_def
  have hinv : (P S)⁻¹ ≤ c := by
    rw [hc_def, ENNReal.ofReal_div_of_pos h1η, ENNReal.ofReal_one, one_div]
    exact ENNReal.inv_le_inv.2 hPS
  have hle : (cond P S).map X ≤ c • P.map X := by
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.map_apply hX hA, Measure.smul_apply, Measure.map_apply hX hA, smul_eq_mul,
      cond_apply hS]
    exact mul_le_mul' hinv (measure_mono Set.inter_subset_right)
  have habs : (cond P S).map X ≪ P.map X := Measure.absolutelyContinuous_of_le_smul hle
  refine ⟨hle, ?_, ?_⟩
  · have hrn : ((cond P S).map X).rnDeriv (P.map X) ≤ᵐ[P.map X] fun _ => c := by
      refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
        fun s hs _ => ?_
      calc ∫⁻ x in s, ((cond P S).map X).rnDeriv (P.map X) x ∂(P.map X)
          ≤ ((cond P S).map X) s := Measure.setLIntegral_rnDeriv_le s
        _ ≤ (c • P.map X) s := Measure.le_iff'.1 hle s
        _ = ∫⁻ _ in s, c ∂(P.map X) := by
          rw [setLIntegral_const, Measure.smul_apply, smul_eq_mul]
    have hess : essSup (((cond P S).map X).rnDeriv (P.map X)) (P.map X) ≤ c :=
      essSup_le_of_ae_le c hrn
    have hne : essSup (((cond P S).map X).rnDeriv (P.map X)) (P.map X) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hess
    have hc0 : IsProbabilityMeasure ((cond P S).map X) ∧ IsProbabilityMeasure (P.map X) ∧
        (cond P S).map X ≪ P.map X := ⟨inferInstance, inferInstance, habs⟩
    unfold ThinShellSampling.renyiInf
    rw [if_pos hc0, if_neg hne]
    apply ENNReal.ofReal_le_ofReal
    have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
    rw [ENNReal.toReal_ofReal hcpos.le] at he
    rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a :=
      essSup (((cond P S).map X).rnDeriv (P.map X)) (P.map X))) with h0 | hpos
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg hcge
    · exact Real.log_le_log hpos he
  · intro q hq
    have hq1 : q ≠ 1 := ne_of_gt hq
    have hq0 : 0 ≤ q := by linarith
    by_cases hac : P.map X ≪ πX
    swap
    · have : ThinShellSampling.renyi q (P.map X) πX = ⊤ := by
        unfold ThinShellSampling.renyi
        rw [if_neg (fun h => hac h.2.2)]
      rw [this, top_add]
      exact le_top
    have hac' : (cond P S).map X ≪ πX := habs.trans hac
    by_cases hI : ∫⁻ x, ((P.map X).rnDeriv πX x) ^ q ∂πX = ⊤
    · have : ThinShellSampling.renyi q (P.map X) πX = ⊤ := by
        have hc2 : IsProbabilityMeasure (P.map X) ∧ IsProbabilityMeasure πX ∧
            P.map X ≪ πX := ⟨inferInstance, inferInstance, hac⟩
        unfold ThinShellSampling.renyi
        simp only [if_pos hc2, if_neg hq1, if_pos hI]
      rw [this, top_add]
      exact le_top
    have hrn : ((cond P S).map X).rnDeriv πX ≤ᵐ[πX]
        fun x => c * (P.map X).rnDeriv πX x := by
      refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
        fun s hs _ => ?_
      calc ∫⁻ x in s, ((cond P S).map X).rnDeriv πX x ∂πX
          ≤ ((cond P S).map X) s := Measure.setLIntegral_rnDeriv_le s
        _ ≤ (c • P.map X) s := Measure.le_iff'.1 hle s
        _ = c * ∫⁻ x in s, (P.map X).rnDeriv πX x ∂πX := by
          rw [Measure.setLIntegral_rnDeriv hac s, Measure.smul_apply, smul_eq_mul]
        _ = ∫⁻ x in s, c * (P.map X).rnDeriv πX x ∂πX :=
          (lintegral_const_mul _ (Measure.measurable_rnDeriv _ _)).symm
    have hIle : ∫⁻ x, (((cond P S).map X).rnDeriv πX x) ^ q ∂πX ≤
        c ^ q * ∫⁻ x, ((P.map X).rnDeriv πX x) ^ q ∂πX := by
      rw [← lintegral_const_mul _ ((Measure.measurable_rnDeriv _ _).pow_const q)]
      apply lintegral_mono_ae
      filter_upwards [hrn] with x hx
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hq0]
      exact ENNReal.rpow_le_rpow hx hq0
    have hcq : c ^ q ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hq0 ENNReal.ofReal_ne_top
    have hÎ : ∫⁻ x, (((cond P S).map X).rnDeriv πX x) ^ q ∂πX ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top hcq hI) hIle
    have hc1 : IsProbabilityMeasure ((cond P S).map X) ∧ IsProbabilityMeasure πX ∧
        (cond P S).map X ≪ πX := ⟨inferInstance, inferInstance, hac'⟩
    have hc2 : IsProbabilityMeasure (P.map X) ∧ IsProbabilityMeasure πX ∧
        P.map X ≪ πX := ⟨inferInstance, inferInstance, hac⟩
    unfold ThinShellSampling.renyi
    simp only [if_pos hc1, if_pos hc2, if_neg hq1, if_neg hÎ, if_neg hI]
    set Î := ∫⁻ x, (((cond P S).map X).rnDeriv πX x) ^ q ∂πX with hÎ_def
    set I := ∫⁻ x, ((P.map X).rnDeriv πX x) ^ q ∂πX with hI_def
    set L := Real.log (1 / (1 - η)) with hL_def
    have hreal : Î.toReal ≤ (1 / (1 - η)) ^ q * I.toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top hcq hI) hIle
      rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, hc_def, ENNReal.toReal_ofReal hcpos.le]
        at this
    rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := Î)) with h0 | hpos
    · rw [← h0, Real.log_zero, zero_div, ENNReal.ofReal_zero]
      exact zero_le
    refine le_trans ?_ ENNReal.ofReal_add_le
    apply ENNReal.ofReal_le_ofReal
    have hApos : 0 < (1 / (1 - η)) ^ q := Real.rpow_pos_of_pos hcpos q
    have hIpos : 0 < I.toReal := by
      rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := I)) with h0 | h
      · rw [← h0, mul_zero] at hreal; linarith
      · exact h
    have key : Real.log Î.toReal ≤ Real.log I.toReal + q * L := by
      have := Real.log_le_log hpos hreal
      rwa [Real.log_mul hApos.ne' hIpos.ne', Real.log_rpow hcpos, add_comm] at this
    rw [div_mul_eq_mul_div, ← add_div]
    exact div_le_div_of_nonneg_right key (by linarith)
