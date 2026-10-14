-- Prove2me | solution 1 for TsitsiklisGittins.IndexTheorem.eq2_2_interchange_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:13:33.927454+00:00
-- url     : https://prove2.me/submissions/09fd3755-9b74-4f28-beda-075a20930724

import Mathlib



namespace TsitsiklisGittins.IndexTheorem

open MeasureTheory

lemma e42_int_exp (β : ℝ) (hβ : 0 < β) (b : ℝ) :
    ∫ t in (0:ℝ)..b, Real.exp (-(β * t)) = (1 - Real.exp (-(β * b))) / β := by
  have h : ∀ x ∈ Set.uIcc 0 b, HasDerivAt (fun t => -(Real.exp (-(β * t))) / β) (Real.exp (-(β * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -β * t) (-β) x := by
      simpa using (hasDerivAt_id' x).const_mul (-β)
    have h2 := (h1.exp).neg.div_const β
    simp only [neg_mul] at h2
    refine h2.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp
  field_simp
  ring

lemma e42_integrableOn_Ioi (β : ℝ) (hβ : 0 < β) :
    IntegrableOn (fun t : ℝ => Real.exp (-(β * t))) (Set.Ioi 0) := by
  have := integrableOn_exp_mul_Ioi (a := -β) (by linarith) 0
  simpa [neg_mul] using this

lemma e42_int_set (β : ℝ) (hβ : 0 < β) (a : ENNReal) :
    ∫ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < a}, Real.exp (-(β * t)) =
      (1 - (if a = ⊤ then 0 else Real.exp (-(β * a.toReal)))) / β := by
  by_cases ha : a = ⊤
  · have : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < a} = Set.Ioi 0 := by
      ext t; simp [ha, Set.mem_Ioi, ENNReal.ofReal_lt_top]
    rw [this, if_pos ha]
    have := integral_exp_mul_Ioi (a := -β) (by linarith) 0
    simp only [neg_mul] at this
    rw [this]
    simp
  · have : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < a} = Set.Ioo 0 a.toReal := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Ioo]
      constructor
      · rintro ⟨h0, h1⟩
        exact ⟨h0, (ENNReal.ofReal_lt_iff_lt_toReal h0.le ha).1 h1⟩
      · rintro ⟨h0, h1⟩
        exact ⟨h0, (ENNReal.ofReal_lt_iff_lt_toReal h0.le ha).2 h1⟩
    rw [this, if_neg ha, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ENNReal.toReal_nonneg]
    exact e42_int_exp β hβ _

theorem eq22_core {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (β : ℝ) (hβ : 0 < β)
    (T : Ω → ℝ) (hT : Measurable T) (hT0 : ∀ ω, 0 ≤ T ω)
    (τ : Ω → ENNReal) (hτ : Measurable τ)
    (rbar : Ω → ℝ → ℝ) (hrbar : Measurable (Function.uncurry rbar))
    (C : ℝ) (hC : ∀ ω t, |rbar ω t| ≤ C)
    (rstar : ℝ) (hle : ∀ ω t, rbar ω t ≤ rstar) :
    ∫ ω, (1 - (if τ ω = ⊤ then 0 else Real.exp (-(β * (τ ω).toReal)))) *
          (∫ t in (0 : ℝ)..T ω, rstar * Real.exp (-(β * t))) ∂P ≥
      ∫ ω, (1 - Real.exp (-(β * T ω))) *
          (∫ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω}, rbar ω t * Real.exp (-(β * t))) ∂P := by
  set A : Ω → ℝ := fun ω => if τ ω = ⊤ then 0 else Real.exp (-(β * (τ ω).toReal)) with hA
  have hAm : Measurable A := by
    apply Measurable.ite (hτ (measurableSet_singleton ⊤)) measurable_const
    exact Real.measurable_exp.comp (measurable_const.mul (ENNReal.measurable_toReal.comp hτ)).neg
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => by simp only [hA]; split_ifs <;> positivity
  have hA1 : ∀ ω, A ω ≤ 1 := fun ω => by
    simp only [hA]; split_ifs
    · norm_num
    · rw [Real.exp_le_one_iff]; have := ENNReal.toReal_nonneg (a := τ ω); nlinarith
  have hE0 : ∀ ω, 0 ≤ 1 - Real.exp (-(β * T ω)) := fun ω => by
    have : Real.exp (-(β * T ω)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hT0 ω]
    linarith
  have hE1 : ∀ ω, 1 - Real.exp (-(β * T ω)) ≤ 1 := fun ω => by
    have := Real.exp_pos (-(β * T ω)); linarith
  have hEm : Measurable (fun ω => 1 - Real.exp (-(β * T ω))) :=
    measurable_const.sub (Real.measurable_exp.comp (measurable_const.mul hT).neg)
  -- LHS integrand
  have hL : ∀ ω, (1 - A ω) * (∫ t in (0 : ℝ)..T ω, rstar * Real.exp (-(β * t))) =
      rstar / β * ((1 - A ω) * (1 - Real.exp (-(β * T ω)))) := by
    intro ω
    rw [intervalIntegral.integral_const_mul, e42_int_exp β hβ]
    field_simp
  -- RHS pointwise
  have hint : ∀ ω, IntegrableOn (fun t => rbar ω t * Real.exp (-(β * t)))
      {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω} := by
    intro ω
    have hm : Measurable (rbar ω) := hrbar.comp measurable_prodMk_left
    have h1 : IntegrableOn (fun t => rbar ω t * Real.exp (-(β * t))) (Set.Ioi 0) := by
      refine Integrable.mono' ((e42_integrableOn_Ioi β hβ).const_mul C) ?_ ?_
      · exact (hm.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun t => ?_
        rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_mul_of_nonneg_right (hC ω t) (Real.exp_pos _).le
    exact h1.mono_set (fun t ht => ht.1)
  have hintE : ∀ ω, IntegrableOn (fun t : ℝ => Real.exp (-(β * t)))
      {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω} := fun ω =>
    (e42_integrableOn_Ioi β hβ).mono_set (fun t ht => ht.1)
  have hpt : ∀ ω, (1 - Real.exp (-(β * T ω))) *
      (∫ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω}, rbar ω t * Real.exp (-(β * t))) ≤
      rstar / β * ((1 - A ω) * (1 - Real.exp (-(β * T ω)))) := by
    intro ω
    have h1 : (∫ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω}, rbar ω t * Real.exp (-(β * t))) ≤
        ∫ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω}, rstar * Real.exp (-(β * t)) :=
      integral_mono (hint ω) ((hintE ω).const_mul rstar)
        (fun t => mul_le_mul_of_nonneg_right (hle ω t) (Real.exp_pos _).le)
    rw [integral_const_mul, e42_int_set β hβ] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hE0 ω)
    refine h2.trans (le_of_eq ?_)
    simp only [hA]
    field_simp
  -- measurability of RHS integrand
  have hF : Measurable (fun ω => ∫ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω}, rbar ω t * Real.exp (-(β * t))) := by
    have hG : Measurable (fun p : Ω × ℝ => if (0 < p.2 ∧ ENNReal.ofReal p.2 < τ p.1) then rbar p.1 p.2 * Real.exp (-(β * p.2)) else 0) := by
      apply Measurable.ite
      · apply MeasurableSet.inter
        · exact measurableSet_lt measurable_const measurable_snd
        · exact measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hτ.comp measurable_fst)
      · exact (hrbar.mul (Real.measurable_exp.comp (measurable_const.mul measurable_snd).neg))
      · exact measurable_const
    have hS : ∀ ω, MeasurableSet {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω} := fun ω =>
      (measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
    have heq : (fun ω => ∫ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω}, rbar ω t * Real.exp (-(β * t))) =
        fun ω => ∫ t : ℝ, (if (0 < t ∧ ENNReal.ofReal t < τ ω) then rbar ω t * Real.exp (-(β * t)) else 0) := by
      funext ω
      rw [← integral_indicator (hS ω)]
      congr 1
      funext t
      simp [Set.indicator]
    rw [heq]
    exact (hG.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  have hRm : Measurable (fun ω => (1 - Real.exp (-(β * T ω))) *
      (∫ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω}, rbar ω t * Real.exp (-(β * t)))) := hEm.mul hF
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (Classical.choice (MeasureTheory.nonempty_of_isProbabilityMeasure P)) 0)
  have hFb : ∀ ω, ‖∫ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω}, rbar ω t * Real.exp (-(β * t))‖ ≤ C / β := by
    intro ω
    have h1 := norm_integral_le_of_norm_le (μ := volume.restrict {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω})
      (f := fun t => rbar ω t * Real.exp (-(β * t))) (g := fun t => C * Real.exp (-(β * t)))
      ((hintE ω).const_mul C) (Filter.Eventually.of_forall (fun t => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_mul_of_nonneg_right (hC ω t) (Real.exp_pos _).le))
    rw [integral_const_mul, e42_int_set β hβ] at h1
    refine h1.trans ?_
    have := hA0 ω
    simp only [hA] at this ⊢
    rw [mul_div_assoc']
    apply div_le_div_of_nonneg_right _ hβ.le
    nlinarith
  have hRi : Integrable (fun ω => (1 - Real.exp (-(β * T ω))) *
      (∫ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω}, rbar ω t * Real.exp (-(β * t)))) P := by
    refine Integrable.of_bound hRm.aestronglyMeasurable (C / β) (Filter.Eventually.of_forall fun ω => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hE0 ω)]
    calc _ ≤ 1 * (C / β) := mul_le_mul (hE1 ω) (hFb ω) (norm_nonneg _) zero_le_one
      _ = C / β := one_mul _
  have hLm : Measurable (fun ω => rstar / β * ((1 - A ω) * (1 - Real.exp (-(β * T ω))))) :=
    measurable_const.mul ((measurable_const.sub hAm).mul hEm)
  have hLi : Integrable (fun ω => rstar / β * ((1 - A ω) * (1 - Real.exp (-(β * T ω))))) P := by
    refine Integrable.of_bound hLm.aestronglyMeasurable (|rstar / β|) (Filter.Eventually.of_forall fun ω => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |(1 - A ω) * (1 - Real.exp (-(β * T ω)))| ≤ 1 := by
      rw [abs_of_nonneg (mul_nonneg (by linarith [hA1 ω]) (hE0 ω))]
      have := hA0 ω; have := hE1 ω
      nlinarith [hA1 ω, hE0 ω]
    calc _ ≤ |rstar / β| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = _ := mul_one _
  have hfun : (fun ω => (1 - A ω) * (∫ t in (0 : ℝ)..T ω, rstar * Real.exp (-(β * t)))) =
      fun ω => rstar / β * ((1 - A ω) * (1 - Real.exp (-(β * T ω)))) := funext hL
  show _ ≥ _
  rw [ge_iff_le]
  rw [hfun]
  exact integral_mono hRi hLi hpt

end TsitsiklisGittins.IndexTheorem

open TsitsiklisGittins.IndexTheorem


theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (β : ℝ) (hβ : 0 < β)
    (T : Ω → ℝ) (hT : Measurable T) (hT0 : ∀ ω, 0 ≤ T ω)
    (τ : Ω → ENNReal) (hτ : Measurable τ)
    (rbar : Ω → ℝ → ℝ) (hrbar : Measurable (Function.uncurry rbar))
    (C : ℝ) (hC : ∀ ω t, |rbar ω t| ≤ C)
    (rstar : ℝ) (hle : ∀ ω t, rbar ω t ≤ rstar) :
    ∫ ω, (1 - (if τ ω = ⊤ then 0 else Real.exp (-(β * (τ ω).toReal)))) *
          (∫ t in (0 : ℝ)..T ω, rstar * Real.exp (-(β * t))) ∂P ≥
      ∫ ω, (1 - Real.exp (-(β * T ω))) *
          (∫ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω}, rbar ω t * Real.exp (-(β * t))) ∂P := by
  exact eq22_core P β hβ T hT hT0 τ hτ rbar hrbar C hC rstar hle
