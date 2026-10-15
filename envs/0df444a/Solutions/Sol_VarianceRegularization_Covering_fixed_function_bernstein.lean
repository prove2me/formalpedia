-- Prove2me | solution 1 for VarianceRegularization.Covering.fixed_function_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T08:30:38.510023+00:00
-- url     : https://prove2.me/submissions/1f1ad430-f8c1-450f-b755-925a851a5ee6

import Mathlib
import Definitions.Def_VarianceRegularization_Covering_robustSup

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace EA2E


lemma pade_pos (u : ℝ) (hu : 0 ≤ u) : (2 - u) * Real.exp u ≤ 2 + u := by
  have hmono : Monotone (fun u : ℝ => (2 + u) - (2 - u) * Real.exp u) := by
    apply monotone_of_deriv_nonneg
    · fun_prop
    · intro x
      have h : HasDerivAt (fun u : ℝ => (2 + u) - (2 - u) * Real.exp u)
          (1 - ((-1) * Real.exp x + (2 - x) * Real.exp x)) x := by
        have h1 : HasDerivAt (fun u : ℝ => 2 + u) 1 x := by
          simpa using (hasDerivAt_id x).const_add 2
        have h2 : HasDerivAt (fun u : ℝ => 2 - u) (-1) x := by
          simpa using (hasDerivAt_id x).const_sub 2
        exact h1.sub (h2.mul (Real.hasDerivAt_exp x))
      rw [h.deriv]
      have := Real.add_one_le_exp (-x)
      have h3 : (1 - x) * Real.exp x ≤ 1 := by
        have := mul_le_mul_of_nonneg_right this (Real.exp_pos x).le
        rw [← Real.exp_add] at this
        simp at this
        nlinarith [this]
      nlinarith [h3]
  have := hmono hu
  simp at this
  linarith

lemma exp_le_quad_neg (u : ℝ) (hu : u ≤ 0) : Real.exp u ≤ 1 + u + u ^ 2 / 2 := by
  have hanti : Antitone (fun u : ℝ => (1 + u + u ^ 2 / 2) - Real.exp u) := by
    apply antitone_of_deriv_nonpos
    · fun_prop
    · intro x
      have h : HasDerivAt (fun u : ℝ => (1 + u + u ^ 2 / 2) - Real.exp u)
          (1 + x - Real.exp x) x := by
        have h1 : HasDerivAt (fun u : ℝ => 1 + u + u ^ 2 / 2) (1 + x) x := by
          have := ((hasDerivAt_id x).const_add 1).add ((hasDerivAt_pow 2 x).div_const 2)
          exact this.congr_deriv (by simp)
        exact h1.sub (Real.hasDerivAt_exp x)
      rw [h.deriv]
      have := Real.add_one_le_exp x
      linarith
  have := hanti hu
  simp at this
  linarith

/-- pointwise Bernstein bound -/
lemma exp_le_bern (u x : ℝ) (hu : u ≤ x) (hx0 : 0 ≤ x) (hx : x < 2) :
    Real.exp u ≤ 1 + u + u ^ 2 / (2 - x) := by
  have h2x : 0 < 2 - x := by linarith
  rcases le_or_gt 0 u with h0 | h0
  · have h2u : 0 < 2 - u := by linarith
    have hp := pade_pos u h0
    have hq : u ^ 2 / (2 - u) ≤ u ^ 2 / (2 - x) :=
      div_le_div_of_nonneg_left (sq_nonneg _) h2x (by linarith)
    have : Real.exp u ≤ 1 + u + u ^ 2 / (2 - u) := by
      rw [← sub_nonneg]
      have : 1 + u + u ^ 2 / (2 - u) - Real.exp u = ((2 + u) - (2 - u) * Real.exp u) / (2 - u) := by
        field_simp; ring
      rw [this]; apply div_nonneg <;> linarith
    linarith
  · have := exp_le_quad_neg u h0.le
    have hq : u ^ 2 / 2 ≤ u ^ 2 / (2 - x) :=
      div_le_div_of_nonneg_left (sq_nonneg _) h2x (by linarith)
    linarith

lemma alg (r b t v : ℝ) (hr : 0 ≤ r) (hb : 0 ≤ b) (ht : 0 < t) (hv : 0 ≤ v)
    (hr2 : r ^ 2 = 2 * v * t) (hD : 0 < r + 5 / 4 * b * t) :
    0 < 2 * t / (r + 5 / 4 * b * t) ∧ 2 * t / (r + 5 / 4 * b * t) * b < 2 ∧
    -(2 * t / (r + 5 / 4 * b * t)) * (r + 2 * (b * t) / 3)
      + v * (2 * t / (r + 5 / 4 * b * t)) ^ 2 / (2 - 2 * t / (r + 5 / 4 * b * t) * b) ≤ -t := by
  obtain ⟨D, hDdef⟩ : ∃ D, D = r + 5 / 4 * b * t := ⟨_, rfl⟩
  rw [← hDdef] at hD ⊢
  have hbt : 0 ≤ b * t := mul_nonneg hb ht.le
  have h1 : 0 < 2 * t / D := by positivity
  have h2 : 2 * t / D * b < 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hD]; nlinarith
  refine ⟨h1, h2, ?_⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = r + b * t / 4 := ⟨_, rfl⟩
  have hE : 0 < E := by rw [hEdef]; nlinarith
  have h3 : 2 - 2 * t / D * b = 2 * E / D := by
    rw [hEdef]; field_simp; rw [hDdef]; ring
  rw [h3]
  have hvt : v = r ^ 2 / (2 * t) := by field_simp; linarith
  rw [hvt, ← sub_nonneg]
  have : -t - (-(2 * t / D) * (r + 2 * (b * t) / 3)
      + r ^ 2 / (2 * t) * (2 * t / D) ^ 2 / (2 * E / D))
      = t * (r * (b * t) / 3 + (b * t) ^ 2 / 48) / (D * E) := by
    field_simp
    rw [hDdef, hEdef]
    ring
  rw [this]
  positivity

lemma int_bdd {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (g : X → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) : Integrable g P :=
  Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

lemma mgf_bound {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (M0 M1 : ℝ) (hM : M0 ≤ M1) (f : X → ℝ) (hf : Measurable f)
    (hfb : ∀ x, f x ∈ Set.Icc M0 M1) (l : ℝ) (hl : 0 < l) (hlb : l * (M1 - M0) < 2) :
    ∫ x, Real.exp (l * (f x - ∫ y, f y ∂P)) ∂P
      ≤ Real.exp (l ^ 2 * variance f P / (2 - l * (M1 - M0))) := by
  set m := ∫ y, f y ∂P with hm
  have hfi : Integrable f P := int_bdd P f hf (|M0| + |M1|) fun x => by
    have := hfb x
    rw [abs_le]; constructor <;> cases abs_cases M0 <;> cases abs_cases M1 <;> linarith [this.1, this.2]
  have hm0 : M0 ≤ m := by
    have : ∫ y, M0 ∂P ≤ ∫ y, f y ∂P := integral_mono (integrable_const _) hfi fun x => (hfb x).1
    simpa using this
  have hm1 : m ≤ M1 := by
    have : ∫ y, f y ∂P ≤ ∫ y, M1 ∂P := integral_mono hfi (integrable_const _) fun x => (hfb x).2
    simpa using this
  have hvar : variance f P = ∫ x, (f x - m) ^ 2 ∂P := variance_eq_integral hf.aemeasurable
  set c := 2 - l * (M1 - M0) with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hb0 : 0 ≤ l * (M1 - M0) := mul_nonneg hl.le (by linarith)
  have hYi : Integrable (fun x => f x - m) P := hfi.sub (integrable_const _)
  have hY2 : Integrable (fun x => (f x - m) ^ 2) P :=
    int_bdd P _ ((hf.sub measurable_const).pow_const 2) ((M1 - M0) ^ 2) fun x => by
      have h1 := hfb x
      rw [abs_of_nonneg (sq_nonneg _)]
      have : |f x - m| ≤ M1 - M0 := by rw [abs_le]; constructor <;> linarith [h1.1, h1.2]
      calc (f x - m) ^ 2 = |f x - m| ^ 2 := (sq_abs _).symm
        _ ≤ (M1 - M0) ^ 2 := by gcongr
  have hexpi : Integrable (fun x => Real.exp (l * (f x - m))) P := by
    refine int_bdd P _ (Real.measurable_exp.comp (measurable_const.mul (hf.sub measurable_const)))
      (Real.exp (l * (M1 - M0))) fun x => ?_
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have h1 := hfb x
    nlinarith [h1.1, h1.2]
  have hrhs : Integrable (fun x => 1 + l * (f x - m) + l ^ 2 * (f x - m) ^ 2 / c) P :=
    ((integrable_const _).add (hYi.const_mul l)).add ((hY2.const_mul (l ^ 2)).div_const c)
  have hpt : ∀ x, Real.exp (l * (f x - m)) ≤ 1 + l * (f x - m) + l ^ 2 * (f x - m) ^ 2 / c := by
    intro x
    have h1 := hfb x
    have := exp_le_bern (l * (f x - m)) (l * (M1 - M0)) (by nlinarith [h1.1, h1.2]) hb0 (by linarith)
    calc _ ≤ _ := this
      _ = _ := by rw [hc]; ring
  have hint := integral_mono hexpi hrhs hpt
  have hcalc : ∫ x, (1 + l * (f x - m) + l ^ 2 * (f x - m) ^ 2 / c) ∂P
      = 1 + l ^ 2 * variance f P / c := by
    have e1 : Integrable (fun x => 1 + l * (f x - m)) P :=
      (integrable_const _).add (hYi.const_mul l)
    have e2 : Integrable (fun x => l ^ 2 * (f x - m) ^ 2 / c) P :=
      (hY2.const_mul (l ^ 2)).div_const c
    have e3 : Integrable (fun x => l * (f x - m)) P := hYi.const_mul l
    have := integral_add (μ := P) e1 e2
    rw [this]
    have h4 := integral_add (μ := P) (integrable_const (1:ℝ)) e3
    rw [h4, integral_const_mul, integral_div, integral_const_mul, ← hvar,
      integral_sub hfi (integrable_const _)]
    have h1 : ∫ a : X, (1:ℝ) ∂P = 1 := by simp
    have h2 : ∫ a : X, m ∂P = m := by simp
    rw [h1, h2, ← hm]
    ring
  rw [hcalc] at hint
  calc _ ≤ _ := hint
    _ ≤ _ := by
      have := Real.add_one_le_exp (l ^ 2 * variance f P / c)
      linarith

lemma mean_mem {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (M0 M1 : ℝ) (f : X → ℝ) (hf : Measurable f)
    (hfb : ∀ x, f x ∈ Set.Icc M0 M1) : M0 ≤ ∫ y, f y ∂P ∧ ∫ y, f y ∂P ≤ M1 := by
  have hfi : Integrable f P := int_bdd P f hf (|M0| + |M1|) fun x => by
    have := hfb x
    rw [abs_le]; constructor <;> cases abs_cases M0 <;> cases abs_cases M1 <;> linarith [this.1, this.2]
  constructor
  · have : ∫ y, M0 ∂P ≤ ∫ y, f y ∂P := integral_mono (integrable_const _) hfi fun x => (hfb x).1
    simpa using this
  · have : ∫ y, f y ∂P ≤ ∫ y, M1 ∂P := integral_mono hfi (integrable_const _) fun x => (hfb x).2
    simpa using this

lemma main {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (M0 M1 : ℝ) (hM : M0 ≤ M1) (f : X → ℝ) (hf : Measurable f)
    (hfb : ∀ x, f x ∈ Set.Icc M0 M1) (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => P)
        {s | ∫ x, f x ∂P + Real.sqrt (2 * variance f P * t / n) + 2 * (M1 - M0) * t / (3 * n)
          < (n : ℝ)⁻¹ * ∑ i, f (s i)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by
  set μ : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => P) with hμ
  set m := ∫ x, f x ∂P with hm
  set σ2 := variance f P with hσ2
  set b := M1 - M0 with hb
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb0 : 0 ≤ b := by rw [hb]; linarith
  have hσ0 : 0 ≤ σ2 := variance_nonneg _ _
  obtain ⟨hm0, hm1⟩ := mean_mem P M0 M1 f hf hfb
  set r := (n : ℝ) * Real.sqrt (2 * σ2 * t / n) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ^ 2 = 2 * ((n : ℝ) * σ2) * t := by
    rw [hr, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  set S : (Fin n → X) → ℝ := ∑ i, (fun ω : Fin n → X => f (ω i) - m) with hS
  have hSapp : ∀ ω, S ω = ∑ i, (f (ω i) - m) := fun ω => by simp [hS, Finset.sum_apply]
  have hsub : {s : Fin n → X | m + Real.sqrt (2 * σ2 * t / n) + 2 * b * t / (3 * n)
      < (n : ℝ)⁻¹ * ∑ i, f (s i)} ⊆ {ω | r + 2 * (b * t) / 3 ≤ S ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hSapp, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 := mul_lt_mul_of_pos_left hω hn'
    have : (n : ℝ) * (m + Real.sqrt (2 * σ2 * t / n) + 2 * b * t / (3 * n))
        = n * m + r + 2 * (b * t) / 3 := by
      rw [hr]; field_simp
    have h2 : (n : ℝ) * ((n : ℝ)⁻¹ * ∑ i, f (ω i)) = ∑ i, f (ω i) := by field_simp
    rw [this, h2] at h1
    linarith
  by_cases hD : 0 < r + 5 / 4 * b * t
  · obtain ⟨hl0, hlb, hexp⟩ := alg r b t ((n : ℝ) * σ2) hr0 hb0 ht (by positivity) hr2 hD
    set l := 2 * t / (r + 5 / 4 * b * t) with hl
    have hmeasY : ∀ i : Fin n, Measurable (fun ω : Fin n → X => f (ω i) - m) := fun i =>
      (hf.comp (measurable_pi_apply i)).sub measurable_const
    have hindep : iIndepFun (fun (i : Fin n) (ω : Fin n → X) => f (ω i) - m) μ :=
      iIndepFun_pi (μ := fun _ : Fin n => P) (X := fun _ x => f x - m)
        (fun _ => (hf.sub measurable_const).aemeasurable)
    have hmgfS : mgf S μ l = ∏ i : Fin n, mgf (fun ω : Fin n → X => f (ω i) - m) μ l :=
      hindep.mgf_sum hmeasY Finset.univ
    have hmgfi : ∀ i : Fin n, mgf (fun ω : Fin n → X => f (ω i) - m) μ l
        = ∫ x, Real.exp (l * (f x - m)) ∂P := by
      intro i
      unfold mgf
      have hmp := measurePreserving_eval (fun _ : Fin n => P) i
      have := integral_map (μ := μ) (φ := fun ω : Fin n → X => ω i)
        (f := fun x : X => Real.exp (l * (f x - m))) (measurable_pi_apply i).aemeasurable
        (Real.measurable_exp.comp (measurable_const.mul (hf.sub measurable_const))).aestronglyMeasurable
      rw [hmp.map_eq] at this
      exact this.symm
    have hone := mgf_bound P M0 M1 hM f hf hfb l hl0 (by rw [← hb]; exact hlb)
    have hmgf_le : mgf S μ l ≤ Real.exp (n * (l ^ 2 * σ2 / (2 - l * b))) := by
      rw [hmgfS, Finset.prod_congr rfl (fun i _ => hmgfi i), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      have hpos : 0 ≤ ∫ x, Real.exp (l * (f x - m)) ∂P := integral_nonneg fun x => (Real.exp_pos _).le
      calc (∫ x, Real.exp (l * (f x - m)) ∂P) ^ n ≤ (Real.exp (l ^ 2 * σ2 / (2 - l * b))) ^ n :=
            pow_le_pow_left₀ hpos hone n
        _ = _ := by rw [← Real.exp_nat_mul]
    have hSmeas : Measurable S := by
      have : S = fun ω => ∑ i, (f (ω i) - m) := funext hSapp
      rw [this]; exact Finset.measurable_sum _ fun i _ => hmeasY i
    have hint : Integrable (fun ω => Real.exp (l * S ω)) μ := by
      refine int_bdd μ _ (Real.measurable_exp.comp (measurable_const.mul hSmeas))
        (Real.exp (l * (n * b))) fun ω => ?_
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hl0.le
      rw [hSapp]
      calc ∑ i, (f (ω i) - m) ≤ ∑ _i : Fin n, b := Finset.sum_le_sum fun i _ => by
            have := hfb (ω i); rw [hb]; linarith [this.2]
        _ = n * b := by simp
    have hch := measure_ge_le_exp_mul_mgf (μ := μ) (X := S) (t := l) (r + 2 * (b * t) / 3) hl0.le hint
    calc μ {s | m + Real.sqrt (2 * σ2 * t / n) + 2 * b * t / (3 * n) < (n : ℝ)⁻¹ * ∑ i, f (s i)}
        ≤ μ {ω | r + 2 * (b * t) / 3 ≤ S ω} := measure_mono hsub
      _ = ENNReal.ofReal (μ.real {ω | r + 2 * (b * t) / 3 ≤ S ω}) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (Real.exp (-t)) := by
        apply ENNReal.ofReal_le_ofReal
        calc μ.real {ω | r + 2 * (b * t) / 3 ≤ S ω}
            ≤ Real.exp (-l * (r + 2 * (b * t) / 3)) * mgf S μ l := hch
          _ ≤ Real.exp (-l * (r + 2 * (b * t) / 3)) * Real.exp (n * (l ^ 2 * σ2 / (2 - l * b))) :=
            mul_le_mul_of_nonneg_left hmgf_le (Real.exp_pos _).le
          _ = Real.exp (-l * (r + 2 * (b * t) / 3) + n * (l ^ 2 * σ2 / (2 - l * b))) :=
            (Real.exp_add _ _).symm
          _ ≤ Real.exp (-t) := by
            apply Real.exp_le_exp.mpr
            have : (n : ℝ) * (l ^ 2 * σ2 / (2 - l * b)) = (n * σ2) * l ^ 2 / (2 - l * b) := by ring
            rw [this]; linarith
  · -- degenerate: b = 0
    have hb00 : b = 0 := by nlinarith [mul_nonneg hb0 ht.le]
    have hempty : {s : Fin n → X | m + Real.sqrt (2 * σ2 * t / n) + 2 * b * t / (3 * n)
        < (n : ℝ)⁻¹ * ∑ i, f (s i)} = ∅ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have hM01 : M1 = M0 := by rw [hb] at hb00; linarith
      have h1 : ∑ i, f (s i) ≤ n * M1 := by
        calc ∑ i, f (s i) ≤ ∑ _i : Fin n, M1 := Finset.sum_le_sum fun i _ => (hfb (s i)).2
          _ = n * M1 := by simp
      have h2 : (n : ℝ)⁻¹ * ∑ i, f (s i) ≤ M1 := by
        calc (n : ℝ)⁻¹ * ∑ i, f (s i) ≤ (n : ℝ)⁻¹ * (n * M1) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = M1 := by field_simp
      have h3 : 0 ≤ Real.sqrt (2 * σ2 * t / n) := Real.sqrt_nonneg _
      have h4 : 0 ≤ 2 * b * t / (3 * n) := by positivity
      linarith
    rw [hempty]; simp


end EA2E

open MeasureTheory ProbabilityTheory VarianceRegularization.Covering in
theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (M0 M1 : ℝ) (hM : M0 ≤ M1) (f : X → ℝ) (hf : Measurable f)
    (hfb : ∀ x, f x ∈ Set.Icc M0 M1) (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => P)
        {s | ∫ x, f x ∂P + Real.sqrt (2 * variance f P * t / n) + 2 * (M1 - M0) * t / (3 * n)
          < empMean f s}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by
  exact EA2E.main P M0 M1 hM f hf hfb n hn t ht
