-- Prove2me | solution 1 for RiskFunctionals.NestedAVaR.condAVaR_pairing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:13:50.49177+00:00
-- url     : https://prove2.me/submissions/7ab2b33e-2a83-4a71-9fc0-446c72d03dc0

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_AverageValueAtRisk

open RiskFunctionals.NestedAVaR

open MeasureTheory

/-- the conditional excess of a globally feasible `W` is a.s. nonnegative -/
theorem g79t_G {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {P : Measure[mΩ] Ω} [IsProbabilityMeasure P] {α : ℝ} (hα₀ : 0 < α)
    {Y V W : Ω → ℝ} (hY : Integrable Y P) (hV : IsConditionalAVaR m P α Y V)
    (hWm : Measurable W) (hW : ∀ᵐ ω ∂P, 0 ≤ W ω ∧ W ω ≤ 1 / α)
    (hWc : P[W|m] =ᵐ[P] fun _ => (1 : ℝ)) :
    Integrable (fun ω => Y ω * W ω - V ω) P ∧
      0 ≤ᵐ[P] P[fun ω => Y ω * W ω - V ω|m] := by
  have hWb : ∀ᵐ ω ∂P, ‖W ω‖ ≤ 1 / α := hW.mono fun ω h => by
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2
  have hYW : Integrable (fun ω => Y ω * W ω) P := hY.mul_bdd hWm.aestronglyMeasurable hWb
  have hWi : Integrable W P := (integrable_const (1 / α)).mono' hWm.aestronglyMeasurable hWb
  have hf : Integrable (fun ω => Y ω * W ω - V ω) P := hYW.sub hV.2.1
  refine ⟨hf, ?_⟩
  have hB : ∀ B, MeasurableSet[m] B → 0 ≤ ∫ ω in B, (Y ω * W ω - V ω) ∂P := by
    intro B hBm
    have hBm' : MeasurableSet B := hm B hBm
    have hfeas : Measurable (B.indicator W) ∧
        (∀ᵐ ω ∂P, 0 ≤ B.indicator W ω ∧ B.indicator W ω ≤ B.indicator (fun _ => 1 / α) ω) ∧
        P[B.indicator W|m] =ᵐ[P] B.indicator (fun _ => (1 : ℝ)) := by
      refine ⟨hWm.indicator hBm', hW.mono fun ω h => ?_, ?_⟩
      · by_cases hω : ω ∈ B
        · simp only [Set.indicator_of_mem hω]; exact h
        · simp only [Set.indicator_of_notMem hω]; exact ⟨le_rfl, le_rfl⟩
      · refine (condExp_indicator hWi hBm).trans ?_
        filter_upwards [hWc] with ω hω
        by_cases h : ω ∈ B
        · simp only [Set.indicator_of_mem h]; exact hω
        · simp only [Set.indicator_of_notMem h]
    have h1 := hV.2.2 B hBm
    have h2 : ((∫ ω in B, V ω ∂P : ℝ) : EReal) ≤ ((∫ ω, Y ω * B.indicator W ω ∂P : ℝ) : EReal) := by
      rw [h1]; exact iInf₂_le (B.indicator W) hfeas
    have h3 : ∫ ω, Y ω * B.indicator W ω ∂P = ∫ ω in B, Y ω * W ω ∂P := by
      rw [← integral_indicator hBm']
      congr 1; funext ω
      by_cases h : ω ∈ B
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [h3] at h2
    have h4 : ∫ ω in B, V ω ∂P ≤ ∫ ω in B, Y ω * W ω ∂P := by exact_mod_cast h2
    rw [integral_sub hYW.integrableOn hV.2.1.integrableOn]
    linarith
  have htr : 0 ≤ᵐ[P.trim hm] P[fun ω => Y ω * W ω - V ω|m] := by
    refine ae_nonneg_of_forall_setIntegral_nonneg
      (integrable_condExp.trim hm stronglyMeasurable_condExp) fun s hs _ => ?_
    rw [← setIntegral_trim hm stronglyMeasurable_condExp hs, setIntegral_condExp hm hf hs]
    exact hB s hs
  exact ae_of_ae_trim hm htr

/-- pairing a bounded `m`-measurable weight with `f` through its conditional expectation -/
theorem g79t_pair {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {P : Measure[mΩ] Ω} [IsProbabilityMeasure P] {f Z : Ω → ℝ} (hf : Integrable f P)
    (hZm : Measurable[m] Z) {C : ℝ} (hZb : ∀ᵐ ω ∂P, |Z ω| ≤ C) :
    Integrable (fun ω => Z ω * f ω) P ∧
    ∫ ω, Z ω * f ω ∂P = ∫ ω, Z ω * P[f|m] ω ∂P := by
  have hZs : StronglyMeasurable[m] Z := hZm.stronglyMeasurable
  have hZb' : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C := hZb.mono fun ω h => by rwa [Real.norm_eq_abs]
  have hZf : Integrable (fun ω => Z ω * f ω) P :=
    hf.bdd_mul (hZs.mono hm).aestronglyMeasurable hZb'
  refine ⟨hZf, ?_⟩
  calc ∫ ω, Z ω * f ω ∂P = ∫ ω, (P[Z * f|m]) ω ∂P := (integral_condExp hm).symm
    _ = ∫ ω, (Z * P[f|m]) ω ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hZs hZf hf)
    _ = _ := rfl

theorem solution {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P] (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    (Y V : Ω → ℝ) (hY : Integrable Y P) (hV : IsConditionalAVaR m P α Y V)
    (Z₁ : Ω → ℝ) (hZ₁m : Measurable[m] Z₁) (hZ₁b : ∃ C : ℝ, ∀ᵐ ω ∂P, |Z₁ ω| ≤ C)
    (hZ₁n : ∀ᵐ ω ∂P, 0 ≤ Z₁ ω) :
    ((∫ ω, V ω * Z₁ ω ∂P : ℝ) : EReal)
      = ⨅ (Z₂ : Ω → ℝ) (_ : Measurable Z₂ ∧
          (∀ᵐ ω ∂P, 0 ≤ Z₂ ω ∧ Z₂ ω ≤ (1 / α) * Z₁ ω) ∧ P[Z₂|m] =ᵐ[P] Z₁),
        ((∫ ω, Y ω * Z₂ ω ∂P : ℝ) : EReal) := by
  obtain ⟨C, hC⟩ := hZ₁b
  have hZ₁m' : Measurable Z₁ := hZ₁m.mono hm le_rfl
  have hZs : StronglyMeasurable[m] Z₁ := hZ₁m.stronglyMeasurable
  have hZb' : ∀ᵐ ω ∂P, ‖Z₁ ω‖ ≤ C := hC.mono fun ω h => by rwa [Real.norm_eq_abs]
  have hVZ : ∫ ω, V ω * Z₁ ω ∂P = ∫ ω, Z₁ ω * V ω ∂P := by simp_rw [mul_comm]
  symm
  apply le_antisymm
  · -- near-optimal global W
    rw [hVZ]
    by_contra hcon
    push_neg at hcon
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hr1' : ∫ ω, Z₁ ω * V ω ∂P < r := by exact_mod_cast hr1
    set C' := max C 0 + 1 with hC'
    have hC'0 : 0 < C' := by positivity
    set ε := (r - ∫ ω, Z₁ ω * V ω ∂P) / C' with hε
    have hε0 : 0 < ε := div_pos (by linarith) hC'0
    have hU := hV.2.2 Set.univ MeasurableSet.univ
    rw [setIntegral_univ] at hU
    have hlt : ((∫ ω, V ω ∂P : ℝ) : EReal) < ((∫ ω, V ω ∂P + ε : ℝ) : EReal) := by
      exact_mod_cast (by linarith)
    rw [hU] at hlt
    obtain ⟨W, hW1⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hWf, hWlt⟩ := iInf_lt_iff.1 hW1
    simp only [Set.indicator_univ] at hWf
    have hWlt' : ∫ ω, Y ω * W ω ∂P < ∫ ω, V ω ∂P + ε := by exact_mod_cast hWlt
    obtain ⟨hWm, hWb, hWc⟩ := hWf
    obtain ⟨hf, hG⟩ := g79t_G hm hα₀ hY hV hWm hWb hWc
    have hWb' : ∀ᵐ ω ∂P, ‖W ω‖ ≤ 1 / α := hWb.mono fun ω h => by
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2
    have hWi : Integrable W P := (integrable_const (1 / α)).mono' hWm.aestronglyMeasurable hWb'
    have hp := g79t_pair hm hf hZ₁m hC
    have hGi : Integrable (P[fun ω => Y ω * W ω - V ω|m]) P := integrable_condExp
    have hZG : Integrable (fun ω => Z₁ ω * P[fun ω => Y ω * W ω - V ω|m] ω) P :=
      hGi.bdd_mul (hZs.mono hm).aestronglyMeasurable hZb'
    have hle1 : ∫ ω, Z₁ ω * P[fun ω => Y ω * W ω - V ω|m] ω ∂P ≤
        ∫ ω, C' * P[fun ω => Y ω * W ω - V ω|m] ω ∂P := by
      refine integral_mono_ae hZG (hGi.const_mul C') ?_
      filter_upwards [hG, hC] with ω h1 h2
      have : Z₁ ω ≤ C' := by
        have := (abs_le.1 h2).2; have := le_max_left C 0; linarith
      exact mul_le_mul_of_nonneg_right this h1
    rw [integral_const_mul, integral_condExp hm,
      integral_sub (hf.add hV.2.1 |>.congr (Filter.Eventually.of_forall fun ω => by simp))
        hV.2.1] at hle1
    have hZV : Integrable (fun ω => Z₁ ω * V ω) P :=
      hV.2.1.bdd_mul (hZs.mono hm).aestronglyMeasurable hZb'
    -- the candidate
    have hfeas : Measurable (fun ω => W ω * Z₁ ω) ∧
        (∀ᵐ ω ∂P, 0 ≤ W ω * Z₁ ω ∧ W ω * Z₁ ω ≤ (1 / α) * Z₁ ω) ∧
        P[fun ω => W ω * Z₁ ω|m] =ᵐ[P] Z₁ := by
      refine ⟨hWm.mul hZ₁m', ?_, ?_⟩
      · filter_upwards [hWb, hZ₁n] with ω h1 h2
        exact ⟨mul_nonneg h1.1 h2, mul_le_mul_of_nonneg_right h1.2 h2⟩
      · have e : (fun ω => W ω * Z₁ ω) = Z₁ * W := by funext ω; simp [mul_comm]
        rw [e]
        have hZW : Integrable (Z₁ * W) P := hWi.bdd_mul (hZs.mono hm).aestronglyMeasurable hZb'
        refine (condExp_mul_of_stronglyMeasurable_left hZs hZW hWi).trans ?_
        filter_upwards [hWc] with ω hω
        simp [hω]
    have hval : ∫ ω, Y ω * (W ω * Z₁ ω) ∂P =
        ∫ ω, Z₁ ω * (Y ω * W ω - V ω) ∂P + ∫ ω, Z₁ ω * V ω ∂P := by
      rw [← integral_add hp.1 hZV]
      congr 1; funext ω; ring
    have hfin : ∫ ω, Y ω * (W ω * Z₁ ω) ∂P < r := by
      rw [hval, hp.2]
      have : C' * (∫ ω, Y ω * W ω ∂P - ∫ ω, V ω ∂P) < C' * ε :=
        mul_lt_mul_of_pos_left (by linarith) hC'0
      have hCε : C' * ε = r - ∫ ω, Z₁ ω * V ω ∂P := by
        rw [hε]; field_simp
      linarith
    have := iInf₂_le (f := fun (Z₂ : Ω → ℝ) (_ : Measurable Z₂ ∧
          (∀ᵐ ω ∂P, 0 ≤ Z₂ ω ∧ Z₂ ω ≤ (1 / α) * Z₁ ω) ∧ P[Z₂|m] =ᵐ[P] Z₁) =>
        ((∫ ω, Y ω * Z₂ ω ∂P : ℝ) : EReal)) _ hfeas
    have h3 : ((∫ ω, Y ω * (W ω * Z₁ ω) ∂P : ℝ) : EReal) < (r : EReal) := by exact_mod_cast hfin
    exact absurd (lt_of_le_of_lt this h3) (not_lt.2 hr2.le)
  · refine le_iInf₂ fun Z₂ hZ₂ => ?_
    obtain ⟨hZ₂m, hZ₂b, hZ₂c⟩ := hZ₂
    set W : Ω → ℝ := fun ω => if 0 < Z₁ ω then Z₂ ω / Z₁ ω else 1 with hWdef
    have hWm : Measurable W :=
      Measurable.ite (measurableSet_lt measurable_const hZ₁m') (hZ₂m.div hZ₁m') measurable_const
    have hWb : ∀ᵐ ω ∂P, 0 ≤ W ω ∧ W ω ≤ 1 / α := by
      filter_upwards [hZ₂b, hZ₁n] with ω h1 h2
      by_cases hz : 0 < Z₁ ω
      · simp only [hWdef, if_pos hz]
        exact ⟨div_nonneg h1.1 h2, (div_le_iff₀ hz).2 h1.2⟩
      · simp only [hWdef, if_neg hz]
        exact ⟨zero_le_one, one_le_one_div hα₀ hα₁⟩
    have hZ₂eq : Z₂ =ᵐ[P] fun ω => W ω * Z₁ ω := by
      filter_upwards [hZ₂b, hZ₁n] with ω h1 h2
      by_cases hz : 0 < Z₁ ω
      · simp only [hWdef, if_pos hz]; field_simp
      · have hz0 : Z₁ ω = 0 := le_antisymm (not_lt.1 hz) h2
        have : Z₂ ω = 0 := le_antisymm (by rw [hz0, mul_zero] at h1; exact h1.2) h1.1
        rw [this, hz0, mul_zero]
    have hWb' : ∀ᵐ ω ∂P, ‖W ω‖ ≤ 1 / α := hWb.mono fun ω h => by
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2
    have hWi : Integrable W P := (integrable_const (1 / α)).mono' hWm.aestronglyMeasurable hWb'
    have hWc : P[W|m] =ᵐ[P] fun _ => (1 : ℝ) := by
      have hZW : Integrable (Z₁ * W) P := hWi.bdd_mul (hZs.mono hm).aestronglyMeasurable hZb'
      have hp1 := condExp_mul_of_stronglyMeasurable_left hZs hZW hWi
      have hp2 : P[Z₁ * W|m] =ᵐ[P] Z₁ := by
        refine (condExp_congr_ae ?_).trans hZ₂c
        filter_upwards [hZ₂eq] with ω hω
        simp [hω, mul_comm]
      have hS : MeasurableSet[m] {ω | Z₁ ω ≤ 0} := measurableSet_le hZ₁m measurable_const
      have hs1 : {ω | Z₁ ω ≤ 0}.indicator W = {ω | Z₁ ω ≤ 0}.indicator (fun _ => (1 : ℝ)) := by
        funext ω
        by_cases h : ω ∈ {ω | Z₁ ω ≤ 0}
        · have h' : ¬ 0 < Z₁ ω := not_lt.2 h
          simp only [Set.indicator_of_mem h, hWdef, if_neg h']
        · simp only [Set.indicator_of_notMem h]
      have hs2 := condExp_indicator hWi hS
      have hs3 : P[{ω | Z₁ ω ≤ 0}.indicator (fun _ => (1 : ℝ))|m] =
          {ω | Z₁ ω ≤ 0}.indicator (fun _ => (1 : ℝ)) :=
        condExp_of_stronglyMeasurable hm (stronglyMeasurable_const.indicator hS)
          ((integrable_const 1).indicator (hm _ hS))
      filter_upwards [hp1, hp2, hs2] with ω h1 h2 h3
      by_cases hz : 0 < Z₁ ω
      · rw [h2, Pi.mul_apply] at h1
        have : Z₁ ω * P[W|m] ω = Z₁ ω * 1 := by rw [mul_one]; exact h1.symm
        exact mul_left_cancel₀ hz.ne' this
      · have hzS : ω ∈ {ω | Z₁ ω ≤ 0} := not_lt.1 hz
        rw [hs1, hs3, Set.indicator_of_mem hzS, Set.indicator_of_mem hzS] at h3
        exact h3.symm
    obtain ⟨hf, hG⟩ := g79t_G hm hα₀ hY hV hWm hWb hWc
    have hp := g79t_pair hm hf hZ₁m hC
    have hZV : Integrable (fun ω => Z₁ ω * V ω) P :=
      hV.2.1.bdd_mul (hZs.mono hm).aestronglyMeasurable hZb'
    have hval : ∫ ω, Y ω * Z₂ ω ∂P =
        ∫ ω, Z₁ ω * (Y ω * W ω - V ω) ∂P + ∫ ω, Z₁ ω * V ω ∂P := by
      rw [← integral_add hp.1 hZV]
      refine integral_congr_ae ?_
      filter_upwards [hZ₂eq] with ω hω
      rw [hω]; ring
    have hnn : 0 ≤ ∫ ω, Z₁ ω * (Y ω * W ω - V ω) ∂P := by
      rw [hp.2]
      refine integral_nonneg_of_ae ?_
      filter_upwards [hZ₁n, hG] with ω h1 h2
      exact mul_nonneg h1 h2
    have : ∫ ω, V ω * Z₁ ω ∂P ≤ ∫ ω, Y ω * Z₂ ω ∂P := by
      rw [hVZ, hval]; linarith
    exact_mod_cast this
