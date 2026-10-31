-- Prove2me | solution 1 for PoolOrNot.Moderate.eq_23
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:29:37.722196+00:00
-- url     : https://prove2.me/submissions/25e829ee-ff90-45e9-b544-d5002d83a0de

import Mathlib
import Definitions.Def_PoolOrNot_Moderate_Waiting

open MeasureTheory ProbabilityTheory

namespace PoolOrNotEq23Aux

/-- partial-fraction coefficient -/
noncomputable def A (c : ℕ → ℝ) (k j : ℕ) : ℝ :=
  ∏ l ∈ (Finset.range k).erase j, c l / (c l - c j)

lemma lagrange_sum (c : ℕ → ℝ) (hinj : Function.Injective c) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), A c (k + 1) j = 1 := by
  have h := Lagrange.sum_basis (s := Finset.range (k + 1)) (v := c)
    (hinj.injOn) ⟨0, by simp⟩
  have h2 := congrArg (Polynomial.eval 0) h
  rw [Polynomial.eval_finset_sum, Polynomial.eval_one] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold A Lagrange.basis
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X]
  rw [zero_sub, div_eq_mul_inv, ← neg_sub, inv_neg]
  ring

lemma A_succ_lt (c : ℕ → ℝ) {k j : ℕ} (hj : j < k) :
    A c (k + 1) j = A c k j * (c k / (c k - c j)) := by
  unfold A
  have : (Finset.range (k + 1)).erase j = insert k ((Finset.range k).erase j) := by
    ext l; simp [Finset.mem_range]; omega
  rw [this, Finset.prod_insert (by simp), mul_comm]

lemma A_succ_self (c : ℕ → ℝ) (hinj : Function.Injective c) (k : ℕ) :
    A c (k + 1) k = 1 - ∑ j ∈ Finset.range k, A c k j * (c k / (c k - c j)) := by
  have h := lagrange_sum c hinj k
  rw [Finset.sum_range_succ] at h
  have : ∑ j ∈ Finset.range k, A c (k + 1) j = ∑ j ∈ Finset.range k, A c k j * (c k / (c k - c j)) :=
    Finset.sum_congr rfl fun j hj => A_succ_lt c (Finset.mem_range.mp hj)
  linarith

noncomputable def G (c : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  if x < 0 then 1 else ∑ j ∈ Finset.range k, A c k j * Real.exp (-c j * x)

lemma integral_expMeasure {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ x, f x ∂(expMeasure r) = ∫ x in Set.Ici 0, r * Real.exp (-r * x) * f x := by
  unfold expMeasure gammaMeasure
  have hpdf : gammaPDF 1 r = fun x => ENNReal.ofReal (gammaPDFReal 1 r x) := rfl
  rw [hpdf, integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDFReal 1 r).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hsplit : ∀ x : ℝ, (ENNReal.ofReal (gammaPDFReal 1 r x)).toReal • f x
      = Set.indicator (Set.Ici 0) (fun x => r * Real.exp (-r * x) * f x) x := by
    intro x
    rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hr x), smul_eq_mul]
    by_cases hx : 0 ≤ x
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hx)]
      simp only [gammaPDFReal, if_pos hx, Real.rpow_one, sub_self, Real.rpow_zero,
        Real.Gamma_one, div_one, mul_one]
      ring_nf
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      simp [gammaPDFReal, hx]
  simp_rw [hsplit]
  rw [integral_indicator measurableSet_Ici]

lemma integral_exp_Ioi {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ∫ e in Set.Ioi x, r * Real.exp (-r * e) = Real.exp (-r * x) := by
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) x]
  field_simp

lemma integrableOn_exp_Ioi {r : ℝ} (hr : 0 < r) (x : ℝ) :
    IntegrableOn (fun e => r * Real.exp (-r * e)) (Set.Ioi x) :=
  (integrableOn_exp_mul_Ioi (by linarith) x).const_mul r

lemma interval_exp {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    ∫ e in (0:ℝ)..x, Real.exp (a * e) = (Real.exp (a * x) - 1) / a := by
  have hd : ∀ e ∈ Set.uIcc (0:ℝ) x, HasDerivAt (fun e => Real.exp (a * e) / a) (Real.exp (a * e)) e := by
    intro e _
    refine (((hasDerivAt_id e).const_mul a).exp.div_const a).congr_deriv ?_
    simp only [id, mul_one]; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp; ring

lemma hypoLaw_prob (rate : ℕ → ℝ) (hr : ∀ k, 0 < rate k) :
    ∀ k, IsProbabilityMeasure (PoolOrNot.Moderate.hypoLaw rate k)
  | 0 => by simp only [PoolOrNot.Moderate.hypoLaw]; infer_instance
  | k + 1 => by
    simp only [PoolOrNot.Moderate.hypoLaw]
    have := hypoLaw_prob rate hr k
    have := isProbabilityMeasure_expMeasure (hr k)
    unfold Measure.conv
    exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma ccdf_hypo (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (hinj : Function.Injective c) :
    ∀ k x, (PoolOrNot.Moderate.hypoLaw c k (Set.Ioi x)).toReal = G c k x
  | 0, x => by
    simp only [PoolOrNot.Moderate.hypoLaw, G, Finset.range_zero, Finset.sum_empty]
    rw [Measure.dirac_apply' _ measurableSet_Ioi]
    by_cases hx : x < 0
    · simp [hx]
    · rw [if_neg hx, Set.indicator_of_notMem (by simpa using hx)]; simp
  | k + 1, x => by
    set P := PoolOrNot.Moderate.hypoLaw c k with hP
    have hPp : IsProbabilityMeasure P := hypoLaw_prob c hc k
    have hEp := isProbabilityMeasure_expMeasure (hc k)
    have IH := ccdf_hypo c hc hinj k
    have hstep : PoolOrNot.Moderate.hypoLaw c (k + 1) (Set.Ioi x)
        = ∫⁻ e, P (Set.Ioi (x - e)) ∂(expMeasure (c k)) := by
      simp only [PoolOrNot.Moderate.hypoLaw]
      rw [← hP]
      unfold Measure.conv
      rw [Measure.map_apply (by fun_prop) measurableSet_Ioi,
        Measure.prod_apply_symm (measurable_add measurableSet_Ioi)]
      congr 1; ext e; congr 1; ext t; simp; constructor <;> intro h <;> linarith
    set h : ℝ → ℝ := fun e => (P (Set.Ioi (x - e))).toReal with hh
    have hmono : Monotone h := by
      intro a b hab
      exact ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (Set.Ioi_subset_Ioi (by linarith)))
    have hlin : ∫⁻ e, P (Set.Ioi (x - e)) ∂(expMeasure (c k)) =
        ∫⁻ e, ENNReal.ofReal (h e) ∂(expMeasure (c k)) := by
      congr 1; ext e; rw [hh]; simp only; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have hint : (PoolOrNot.Moderate.hypoLaw c (k + 1) (Set.Ioi x)).toReal
        = ∫ e, h e ∂(expMeasure (c k)) := by
      rw [hstep, hlin, integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun e => ENNReal.toReal_nonneg)
        hmono.measurable.aestronglyMeasurable]
    rw [hint, integral_expMeasure (hc k)]
    have hhG : ∀ e, h e = G c k (x - e) := fun e => IH (x - e)
    set r := c k with hr
    have hr0 : 0 < r := hc k
    by_cases hx : x < 0
    · -- everything is 1
      have : ∫ e in Set.Ici 0, r * Real.exp (-r * e) * h e
          = ∫ e in Set.Ioi 0, r * Real.exp (-r * e) := by
        rw [integral_Ici_eq_integral_Ioi]
        refine setIntegral_congr_fun measurableSet_Ioi fun e he => ?_
        rw [hhG, G, if_pos (by simp at he; linarith)]; ring
      rw [this, integral_exp_Ioi hr0, G, if_pos hx]; simp
    · push Not at hx
      have hsplit : Set.Ici (0:ℝ) = Set.Icc 0 x ∪ Set.Ioi x := by
        ext e; simp; constructor
        · intro he; by_cases hex : e ≤ x
          · left; exact ⟨he, hex⟩
          · right; linarith
        · rintro (⟨h1, -⟩ | h1) <;> linarith
      -- explicit integrand on [0, x]
      set F : ℝ → ℝ := fun e => ∑ j ∈ Finset.range k,
        (A c k j * r * Real.exp (-c j * x)) * Real.exp ((c j - r) * e) with hF
      have hIcc : ∀ e ∈ Set.Icc (0:ℝ) x, r * Real.exp (-r * e) * h e = F e := by
        intro e he
        rw [hhG, G, if_neg (by simp at he; linarith), hF, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have : Real.exp (-r * e) * Real.exp (-c j * (x - e))
            = Real.exp (-c j * x) * Real.exp ((c j - r) * e) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        calc r * Real.exp (-r * e) * (A c k j * Real.exp (-c j * (x - e)))
            = A c k j * r * (Real.exp (-r * e) * Real.exp (-c j * (x - e))) := by ring
          _ = _ := by rw [this]; ring
      have hIoi : ∀ e ∈ Set.Ioi x, r * Real.exp (-r * e) * h e = r * Real.exp (-r * e) := by
        intro e he
        rw [hhG, G, if_pos (by simp at he; linarith)]; ring
      have hFc : Continuous F := by rw [hF]; fun_prop
      rw [hsplit, setIntegral_union (Set.disjoint_left.mpr fun e h1 h2 => by simp at h1 h2; linarith) measurableSet_Ioi
        ((hFc.integrableOn_Icc).congr_fun (fun e he => (hIcc e he).symm) measurableSet_Icc)
        ((integrableOn_exp_Ioi hr0 x).congr_fun (fun e he => (hIoi e he).symm) measurableSet_Ioi),
        setIntegral_congr_fun measurableSet_Icc hIcc, setIntegral_congr_fun measurableSet_Ioi hIoi,
        integral_exp_Ioi hr0, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx,
        hF, intervalIntegral.integral_finsetSum (fun j _ => by
          apply Continuous.intervalIntegrable; fun_prop)]
      simp_rw [intervalIntegral.integral_const_mul]
      have hne : ∀ j ∈ Finset.range k, c j - r ≠ 0 := by
        intro j hj; rw [hr]; intro h0
        have := hinj (by linarith : c j = c k)
        simp at hj; omega
      rw [Finset.sum_congr rfl fun j hj => by rw [interval_exp (hne j hj) x]]
      rw [G, if_neg (by linarith), Finset.sum_range_succ, A_succ_self c hinj k]
      have hs : ∑ j ∈ Finset.range k, A c (k + 1) j * Real.exp (-c j * x)
          = ∑ j ∈ Finset.range k, A c k j * (r / (r - c j)) * Real.exp (-c j * x) :=
        Finset.sum_congr rfl fun j hj => by rw [A_succ_lt c (Finset.mem_range.mp hj)]
      rw [← hr, hs]
      have hexp : ∀ j, Real.exp (-c j * x) * Real.exp ((c j - r) * x) = Real.exp (-r * x) := by
        intro j; rw [← Real.exp_add]; ring_nf
      have key : ∀ j ∈ Finset.range k,
          A c k j * r * Real.exp (-c j * x) * ((Real.exp ((c j - r) * x) - 1) / (c j - r))
          = A c k j * (r / (r - c j)) * Real.exp (-c j * x)
            - A c k j * (r / (r - c j)) * Real.exp (-r * x) := by
        intro j hj
        have h1 := hne j hj
        have h2 : r - c j ≠ 0 := by intro h0; apply h1; linarith
        rw [← hexp j]
        field_simp
        ring
      rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, sub_mul, one_mul, Finset.sum_mul]
      ring

end PoolOrNotEq23Aux

open PoolOrNot.Moderate in
theorem solution (μ θ : ℝ) (hμ : 0 < μ) (hθ : 0 < θ) (i : ℕ) (hi : 1 ≤ i) (x : ℝ) (hx : 0 ≤ x) :
    (taLaw μ θ i (Set.Ioi x)).toReal =
      ∑ j ∈ Finset.Icc 1 i, Real.exp (-(μ + ((j : ℝ) - 1) * θ) * x) *
        ∏ k ∈ (Finset.Icc 1 i).erase j, (μ + ((k : ℝ) - 1) * θ) / (((k : ℝ) - (j : ℝ)) * θ) := by
  set c : ℕ → ℝ := fun k => μ + (k : ℝ) * θ with hc
  have hcpos : ∀ k, 0 < c k := fun k => by rw [hc]; positivity
  have hinj : Function.Injective c := by
    intro a b hab
    simp only [hc] at hab
    have : (a : ℝ) = b := by
      have := mul_right_cancel₀ hθ.ne' (by linarith : (a : ℝ) * θ = b * θ); exact this
    exact_mod_cast this
  unfold taLaw
  rw [PoolOrNotEq23Aux.ccdf_hypo c hcpos hinj i x, PoolOrNotEq23Aux.G, if_neg (by linarith)]
  have hIcc : Finset.Icc 1 i = (Finset.range i).image (· + 1) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h; exact ⟨j - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega
  have hinj1 : Function.Injective (fun j : ℕ => j + 1) := fun a b h => by simpa using h
  rw [hIcc, Finset.sum_image (fun a _ b _ h => hinj1 h)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mul_comm]
  congr 1
  · congr 1; simp [hc]
  · unfold PoolOrNotEq23Aux.A
    rw [← Finset.image_erase hinj1, Finset.prod_image (fun a _ b _ h => hinj1 h)]
    refine Finset.prod_congr rfl fun l hl => ?_
    simp only [hc]; push_cast; ring_nf
