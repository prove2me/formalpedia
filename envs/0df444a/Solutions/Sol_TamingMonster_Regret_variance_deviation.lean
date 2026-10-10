-- Prove2me | solution 1 for TamingMonster.Regret.variance_deviation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T02:45:52.414109+00:00
-- url     : https://prove2.me/submissions/daa07ba3-67a6-42b6-998f-9f0f601d034f

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm
import Definitions.Def_TamingMonster_Regret_Analysis

set_option autoImplicit false

namespace VDev

open MeasureTheory ProbabilityTheory TamingMonster.Regret

/-- `exp (-u) ≤ 1 - u/2` on `[0, 1/2]`. -/
theorem exp_neg_le_half (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) : Real.exp (-u) ≤ 1 - u / 2 := by
  have habs : |(-u)| ≤ 1 := by rw [abs_neg, abs_of_nonneg h0]; linarith
  have := Real.abs_exp_sub_one_sub_id_le habs
  have h2 := (abs_le.mp this).2
  nlinarith

/-- Chernoff lower tail for a bounded nonnegative function of i.i.d. samples. -/
theorem chernoff_lower {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure X) [IsProbabilityMeasure ν]
    (x : ℕ → Ω → X) (hxmeas : ∀ t, Measurable (x t))
    (hxind : iIndepFun x P) (hxlaw : ∀ t, P.map (x t) = ν)
    (g : X → ℝ) (hg : Measurable g) (B : ℝ) (hB : 0 < B) (hg0 : ∀ y, 0 ≤ g y)
    (hgB : ∀ y, g y ≤ B) (n : ℕ) (hn : 1 ≤ n) (δ' : ℝ) (hδ' : 0 < δ') :
    P {ω | ¬ (∫ y, g y ∂ν ≤ 2 * ((∑ i ∈ Finset.Icc 1 n, g (x i ω)) / n)
        + 4 * B * Real.log (1 / δ') / n)} ≤ ENNReal.ofReal δ' := by
  set E := ∫ y, g y ∂ν with hE
  set lam : ℝ := 1 / (2 * B) with hlam
  have hlam0 : 0 < lam := by positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let Y : ℕ → Ω → ℝ := fun i => g ∘ x i
  have hYmeas : ∀ i, Measurable (Y i) := fun i => hg.comp (hxmeas i)
  have hYind : iIndepFun Y P := hxind.comp (fun _ => g) (fun _ => hg)
  set S : Ω → ℝ := ∑ i ∈ Finset.Icc 1 n, Y i with hS
  have hSapp : ∀ ω, S ω = ∑ i ∈ Finset.Icc 1 n, g (x i ω) := by
    intro ω; simp [S, Y, Finset.sum_apply]
  have hSmeas : Measurable S := by
    rw [show S = fun ω => ∑ i ∈ Finset.Icc 1 n, Y i ω from funext (fun ω => Finset.sum_apply ω _ _)]
    exact Finset.measurable_sum _ (fun i _ => hYmeas i)
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => by
    rw [hSapp]; exact Finset.sum_nonneg (fun i _ => hg0 _)
  set ε : ℝ := n * E / 2 - 2 * B * Real.log (1 / δ') with hε
  have hsub : {ω | ¬ (E ≤ 2 * ((∑ i ∈ Finset.Icc 1 n, g (x i ω)) / n)
        + 4 * B * Real.log (1 / δ') / n)} ⊆ {ω | S ω ≤ ε} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, not_le] at hω ⊢
    rw [hSapp, hε]
    rw [mul_div_assoc'] at hω
    have h1 : 2 * (∑ i ∈ Finset.Icc 1 n, g (x i ω)) / n + 4 * B * Real.log (1 / δ') / n
        = (2 * (∑ i ∈ Finset.Icc 1 n, g (x i ω)) + 4 * B * Real.log (1 / δ')) / n := by ring
    rw [h1, div_lt_iff₀ hnR] at hω
    linarith
  have hint : Integrable (fun ω => Real.exp (-lam * S ω)) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · exact (Real.measurable_exp.comp (hSmeas.const_mul _)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      have := hS0 ω
      nlinarith
  have hchern := measure_le_le_exp_mul_mgf (X := S) (μ := P) ε (t := -lam) (by linarith) hint
  -- bound each mgf factor
  have hgint : Integrable g ν := by
    refine Integrable.mono' (integrable_const B) hg.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 y)]; exact hgB y
  have hmgf1 : ∀ i, mgf (Y i) P (-lam) ≤ Real.exp (-(lam * E / 2)) := by
    intro i
    have hmap : mgf (Y i) P (-lam) = ∫ y, Real.exp (-lam * g y) ∂ν := by
      rw [mgf, ← hxlaw i, integral_map (hxmeas i).aemeasurable]
      · rfl
      · exact (Real.measurable_exp.comp (hg.const_mul _)).aestronglyMeasurable
    rw [hmap]
    have hpt : ∀ y, Real.exp (-lam * g y) ≤ 1 - lam * g y / 2 := by
      intro y
      have h0 : 0 ≤ lam * g y := mul_nonneg hlam0.le (hg0 y)
      have h1 : lam * g y ≤ 1 / 2 := by
        rw [hlam, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        linarith [hgB y]
      have := exp_neg_le_half (lam * g y) h0 h1
      rwa [neg_mul]
    have hint2 : Integrable (fun y => Real.exp (-lam * g y)) ν := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
      · exact (Real.measurable_exp.comp (hg.const_mul _)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_one_iff.mpr
        have := hg0 y
        nlinarith
    calc ∫ y, Real.exp (-lam * g y) ∂ν ≤ ∫ y, (1 - lam * g y / 2) ∂ν :=
          integral_mono hint2 ((integrable_const 1).sub ((hgint.const_mul lam).div_const 2)) hpt
      _ = 1 - lam * E / 2 := by
          rw [integral_sub (integrable_const 1) ((hgint.const_mul lam).div_const 2),
            integral_div, integral_const_mul]
          simp [hE]
      _ ≤ Real.exp (-(lam * E / 2)) := by
          have := Real.add_one_le_exp (-(lam * E / 2)); linarith
  have hmgf : mgf S P (-lam) ≤ Real.exp (-(lam * E / 2)) ^ n := by
    rw [hS, hYind.mgf_sum hYmeas]
    calc ∏ i ∈ Finset.Icc 1 n, mgf (Y i) P (-lam)
        ≤ ∏ i ∈ Finset.Icc 1 n, Real.exp (-(lam * E / 2)) :=
          Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => hmgf1 i)
      _ = Real.exp (-(lam * E / 2)) ^ n := by simp
  have hfinal : Real.exp (- -lam * ε) * mgf S P (-lam) ≤ δ' := by
    calc Real.exp (- -lam * ε) * mgf S P (-lam)
        ≤ Real.exp (- -lam * ε) * Real.exp (-(lam * E / 2)) ^ n :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ = Real.exp (- -lam * ε + n * (-(lam * E / 2))) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ = Real.exp (Real.log δ') := by
          congr 1
          rw [hε, hlam, Real.log_div one_ne_zero hδ'.ne', Real.log_one]
          field_simp
          ring
      _ = δ' := Real.exp_log hδ'
  calc P {ω | ¬ (E ≤ 2 * ((∑ i ∈ Finset.Icc 1 n, g (x i ω)) / n)
        + 4 * B * Real.log (1 / δ') / n)} ≤ P {ω | S ω ≤ ε} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | S ω ≤ ε}) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal δ' := ENNReal.ofReal_le_ofReal (hchern.trans hfinal)


/-- Averaging bounds for `1/(c s/N + μ)` under weights with given first and second moments. -/
theorem avg_bounds {ι : Type*} [Fintype ι] (w s : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hs0 : ∀ i, 0 ≤ s i) (N : ℕ) (hN : 0 < N) (q : ℝ) (hq0 : 0 ≤ q)
    (hs1 : ∑ i, w i * s i = N * q) (hs2 : ∑ i, w i * s i ^ 2 ≤ N * q + (N : ℝ) ^ 2 * q ^ 2)
    (c μ : ℝ) (hc0 : 0 ≤ c) (hμ : 0 < μ) (hNμ : c ≤ N * μ) :
    1 / (c * q + μ) ≤ ∑ i, w i * (1 / (c * (s i / N) + μ)) ∧
      ∑ i, w i * (1 / (c * (s i / N) + μ)) ≤ 2 / (c * q + μ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set yb := c * q + μ with hyb
  have hyb0 : 0 < yb := by positivity
  set d : ι → ℝ := fun i => c * (s i / N) + μ - yb with hd
  have hy : ∀ i, μ ≤ c * (s i / N) + μ := fun i => by
    have := hs0 i; have : 0 ≤ c * (s i / N) := by positivity
    linarith
  have hy0 : ∀ i, 0 < c * (s i / N) + μ := fun i => lt_of_lt_of_le hμ (hy i)
  -- moment identities
  have hd1 : ∑ i, w i * d i = 0 := by
    have : ∑ i, w i * d i = (c / N) * ∑ i, w i * s i + (μ - yb) * ∑ i, w i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by simp only [hd]; ring)
    rw [this, hs1, hw1, hyb]; field_simp; ring
  have hd2 : ∑ i, w i * d i ^ 2 ≤ c ^ 2 * q / N := by
    have : ∑ i, w i * d i ^ 2 = (c / N) ^ 2 * ∑ i, w i * s i ^ 2
        + (2 * (c / N) * (μ - yb)) * ∑ i, w i * s i + (μ - yb) ^ 2 * ∑ i, w i := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by simp only [hd]; ring)
    rw [this, hs1, hw1]
    have hcn : 0 ≤ (c / N) ^ 2 := sq_nonneg _
    have h2 := mul_le_mul_of_nonneg_left hs2 hcn
    have : (c / ↑N) ^ 2 * (↑N * q + ↑N ^ 2 * q ^ 2) + 2 * (c / ↑N) * (μ - yb) * (↑N * q)
        + (μ - yb) ^ 2 * 1 = c ^ 2 * q / N := by
      rw [hyb]; field_simp; ring
    linarith
  constructor
  · -- Jensen: 1/y ≥ 1/yb - d/yb²
    have hpt : ∀ i, w i * (1 / yb - d i / yb ^ 2) ≤ w i * (1 / (c * (s i / N) + μ)) := by
      intro i
      apply mul_le_mul_of_nonneg_left _ (hw0 i)
      have hyi := hy0 i
      have hdi : c * (s i / N) + μ = yb + d i := by simp only [hd]; ring
      rw [hdi] at hyi ⊢
      rw [div_sub_div _ _ hyb0.ne' (by positivity), div_le_div_iff₀ (by positivity) hyi]
      nlinarith [sq_nonneg (d i), sq_nonneg yb, mul_pos hyb0 hyb0, sq_nonneg (d i * yb)]
    have hsum : ∑ i, w i * (1 / yb - d i / yb ^ 2) = 1 / yb := by
      have : ∑ i, w i * (1 / yb - d i / yb ^ 2) = (1 / yb) * ∑ i, w i
          - (1 / yb ^ 2) * ∑ i, w i * d i := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [this, hw1, hd1]; ring
    rw [← hsum]
    exact Finset.sum_le_sum (fun i _ => hpt i)
  · have hpt : ∀ i, w i * (1 / (c * (s i / N) + μ))
        ≤ w i * (1 / yb - d i / yb ^ 2 + d i ^ 2 / (yb ^ 2 * μ)) := by
      intro i
      apply mul_le_mul_of_nonneg_left _ (hw0 i)
      have hyi := hy0 i
      have hyμ := hy i
      have hdi : c * (s i / N) + μ = yb + d i := by simp only [hd]; ring
      rw [hdi] at hyi hyμ ⊢
      have hid : 1 / (yb + d i) = 1 / yb - d i / yb ^ 2 + d i ^ 2 / (yb ^ 2 * (yb + d i)) := by
        field_simp; ring
      rw [hid]
      have : d i ^ 2 / (yb ^ 2 * (yb + d i)) ≤ d i ^ 2 / (yb ^ 2 * μ) := by
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left hyμ (sq_nonneg _)
      linarith
    have hsum : ∑ i, w i * (1 / yb - d i / yb ^ 2 + d i ^ 2 / (yb ^ 2 * μ))
        = 1 / yb - (1 / yb ^ 2) * ∑ i, w i * d i + (1 / (yb ^ 2 * μ)) * ∑ i, w i * d i ^ 2 := by
      have : ∑ i, w i * (1 / yb - d i / yb ^ 2 + d i ^ 2 / (yb ^ 2 * μ)) = (1 / yb) * ∑ i, w i
          - (1 / yb ^ 2) * ∑ i, w i * d i + (1 / (yb ^ 2 * μ)) * ∑ i, w i * d i ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [this, hw1]; ring
    calc ∑ i, w i * (1 / (c * (s i / N) + μ))
        ≤ ∑ i, w i * (1 / yb - d i / yb ^ 2 + d i ^ 2 / (yb ^ 2 * μ)) :=
          Finset.sum_le_sum (fun i _ => hpt i)
      _ = 1 / yb - (1 / yb ^ 2) * ∑ i, w i * d i
            + (1 / (yb ^ 2 * μ)) * ∑ i, w i * d i ^ 2 := hsum
      _ ≤ 1 / yb + (1 / (yb ^ 2 * μ)) * (c ^ 2 * q / N) := by
          rw [hd1]
          have : 0 ≤ 1 / (yb ^ 2 * μ) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hd2 this]
      _ ≤ 2 / yb := by
          have key : c ^ 2 * q / N ≤ yb * μ := by
            rw [div_le_iff₀ hNR]
            have hcq : c * q ≤ yb := by rw [hyb]; linarith
            have h1 : c * (c * q) ≤ (N * μ) * yb :=
              mul_le_mul hNμ hcq (by positivity) (by positivity)
            nlinarith
          have : (1 / (yb ^ 2 * μ)) * (c ^ 2 * q / N) ≤ (1 / (yb ^ 2 * μ)) * (yb * μ) :=
            mul_le_mul_of_nonneg_left key (by positivity)
          have h3 : (1 / (yb ^ 2 * μ)) * (yb * μ) = 1 / yb := by field_simp
          rw [h3] at this
          have : 2 / yb = 1 / yb + 1 / yb := by ring
          linarith

/-- Product weights. -/
theorem sum_prod_weights {ι : Type*} [Fintype ι] (Q : ι → ℝ) (N : ℕ) (F : Fin N → ι → ℝ) :
    ∑ σ : Fin N → ι, ∏ i, (Q (σ i) * F i (σ i)) = ∏ i, ∑ p, Q p * F i p :=
  (Fintype.prod_sum (fun i p => Q p * F i p)).symm

theorem moment0 {ι : Type*} [Fintype ι] (Q : ι → ℝ) (hQ1 : ∑ p, Q p = 1) (N : ℕ) :
    ∑ σ : Fin N → ι, ∏ i, Q (σ i) = 1 := by
  have := sum_prod_weights Q N (fun _ _ => 1)
  simp only [mul_one] at this
  rw [this, hQ1]; simp

theorem moment1 {ι : Type*} [Fintype ι] (Q : ι → ℝ) (hQ1 : ∑ p, Q p = 1) (N : ℕ)
    (h : ι → ℝ) (j : Fin N) :
    ∑ σ : Fin N → ι, (∏ i, Q (σ i)) * h (σ j) = ∑ p, Q p * h p := by
  have := sum_prod_weights Q N (fun i p => if i = j then h p else 1)
  have e1 : ∀ σ : Fin N → ι, ∏ i, (Q (σ i) * (if i = j then h (σ i) else 1))
      = (∏ i, Q (σ i)) * h (σ j) := by
    intro σ
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j, if_pos (Finset.mem_univ _)]
  have e2 : ∀ i, ∑ p, Q p * (if i = j then h p else 1) = if i = j then ∑ p, Q p * h p else 1 := by
    intro i
    split_ifs
    · rfl
    · simp [hQ1]
  simp only [e1, e2] at this
  rw [this, Finset.prod_ite_eq' Finset.univ j, if_pos (Finset.mem_univ _)]

theorem moment2_ne {ι : Type*} [Fintype ι] (Q : ι → ℝ) (hQ1 : ∑ p, Q p = 1) (N : ℕ)
    (h : ι → ℝ) (j k : Fin N) (hjk : j ≠ k) :
    ∑ σ : Fin N → ι, (∏ i, Q (σ i)) * (h (σ j) * h (σ k)) = (∑ p, Q p * h p) ^ 2 := by
  have := sum_prod_weights Q N (fun i p => (if i = j then h p else 1) * (if i = k then h p else 1))
  have e1 : ∀ σ : Fin N → ι, ∏ i, (Q (σ i) * ((if i = j then h (σ i) else 1)
      * (if i = k then h (σ i) else 1))) = (∏ i, Q (σ i)) * (h (σ j) * h (σ k)) := by
    intro σ
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j,
      Finset.prod_ite_eq' Finset.univ k, if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  have e2 : ∀ i, ∑ p, Q p * ((if i = j then h p else 1) * (if i = k then h p else 1))
      = (if i = j then ∑ p, Q p * h p else 1) * (if i = k then ∑ p, Q p * h p else 1) := by
    intro i
    by_cases h1 : i = j
    · have h2 : i ≠ k := by rw [h1]; exact hjk
      simp only [if_pos h1, if_neg h2, mul_one]
    · by_cases h2 : i = k
      · simp only [if_neg h1, if_pos h2, one_mul]
      · simp [h1, h2, hQ1]
  simp only [e1, e2] at this
  rw [this, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j,
    Finset.prod_ite_eq' Finset.univ k, if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  ring


theorem measurable_eval_pair {K : ℕ} :
    Measurable (fun fa : (Fin K → ℝ) × Fin K => fa.1 fa.2) :=
  measurable_from_prod_countable_left (fun a => measurable_pi_apply a)

theorem measurable_smoothProj {X : Type*} [MeasurableSpace X] {K : ℕ}
    (Pi : Finset (X → Fin K)) (hPiMeas : ∀ π ∈ Pi, Measurable π) (Q : Pi → ℝ) (μ : ℝ) :
    Measurable (fun x => smoothProj Pi Q μ x) := by
  classical
  apply measurable_pi_lambda
  intro a
  unfold smoothProj
  simp_rw [Finset.sum_filter]
  apply Measurable.add_const
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro π _
  apply Measurable.ite _ measurable_const measurable_const
  exact (hPiMeas π π.2) (measurableSet_singleton a)

open Classical in
/-- Empirical weights of a sequence of policies. -/
noncomputable def emp {X : Type*} {K : ℕ} {Pi : Finset (X → Fin K)} {N : ℕ} (σ : Fin N → Pi) :
    Pi → ℝ :=
  fun p => (∑ i, if σ i = p then (1 : ℝ) else 0) / N

theorem emp_nonneg {X : Type*} {K : ℕ} {Pi : Finset (X → Fin K)} {N : ℕ} (σ : Fin N → Pi)
    (p : Pi) : 0 ≤ emp σ p := by
  unfold emp
  exact div_nonneg (Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)) (Nat.cast_nonneg _)

theorem smoothProj_eq_ind {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ) (μ : ℝ)
    (x : X) (a : Fin K) :
    smoothProj Pi Q μ x a
      = (1 - (K : ℝ) * μ) * ∑ p : Pi, Q p * (if (p : X → Fin K) x = a then 1 else 0) + μ := by
  unfold smoothProj
  rw [Finset.sum_filter]
  congr 2
  exact Finset.sum_congr rfl (fun p _ => by split_ifs <;> simp)

theorem emp_sum {X : Type*} {K : ℕ} {Pi : Finset (X → Fin K)} {N : ℕ} (σ : Fin N → Pi)
    (h : Pi → ℝ) : ∑ p, emp σ p * h p = (∑ i, h (σ i)) / N := by
  classical
  unfold emp
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [ite_mul]

theorem sp_ge {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ) (hQ0 : ∀ p, 0 ≤ Q p)
    (μ : ℝ) (hKμ : (K : ℝ) * μ ≤ 1) (x : X) (a : Fin K) : μ ≤ smoothProj Pi Q μ x a := by
  unfold smoothProj
  have := Finset.sum_nonneg (fun π (_ : π ∈ Finset.univ.filter
    (fun π : Pi => (π : X → Fin K) x = a)) => hQ0 π)
  have h1 : 0 ≤ 1 - (K : ℝ) * μ := by linarith
  nlinarith

theorem pointwise_sparsify {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ)
    (hQ0 : ∀ p, 0 ≤ Q p) (hQ1 : ∑ p, Q p = 1) (μ : ℝ) (hμ : 0 < μ) (hKμ : (K : ℝ) * μ ≤ 1)
    (N : ℕ) (hN : 0 < N) (hNμ : 1 - (K : ℝ) * μ ≤ N * μ) (x : X) (a : Fin K) :
    1 / smoothProj Pi Q μ x a
        ≤ ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * (1 / smoothProj Pi (emp σ) μ x a) ∧
      ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * (1 / smoothProj Pi (emp σ) μ x a)
        ≤ 2 / smoothProj Pi Q μ x a := by
  classical
  set h : Pi → ℝ := fun p => if (p : X → Fin K) x = a then 1 else 0 with hh
  set q := ∑ p, Q p * h p with hq
  have hspQ : smoothProj Pi Q μ x a = (1 - (K : ℝ) * μ) * q + μ := smoothProj_eq_ind Pi Q μ x a
  have hspE : ∀ σ : Fin N → Pi,
      smoothProj Pi (emp σ) μ x a = (1 - (K : ℝ) * μ) * ((∑ i, h (σ i)) / N) + μ := by
    intro σ; rw [smoothProj_eq_ind, emp_sum]
  simp only [hspQ, hspE]
  have hh01 : ∀ p, 0 ≤ h p ∧ h p * h p = h p := fun p => by
    simp only [hh]; split_ifs <;> norm_num
  have hq0 : 0 ≤ q := Finset.sum_nonneg (fun p _ => mul_nonneg (hQ0 p) (hh01 p).1)
  have hw0 : ∀ σ : Fin N → Pi, 0 ≤ ∏ i, Q (σ i) := fun σ => Finset.prod_nonneg (fun i _ => hQ0 _)
  have hs1 : ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * (∑ i, h (σ i)) = N * q := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [moment1 Q hQ1 N h]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rfl
  have hterm : ∀ j k : Fin N, ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * (h (σ j) * h (σ k))
      ≤ (if j = k then q else 0) + q ^ 2 := by
    intro j k
    by_cases hjk : j = k
    · subst hjk
      rw [moment1 Q hQ1 N (fun p => h p * h p) j]
      have : ∑ p, Q p * (h p * h p) = q :=
        Finset.sum_congr rfl (fun p _ => by rw [(hh01 p).2])
      rw [this, if_pos rfl]
      nlinarith [sq_nonneg q]
    · rw [moment2_ne Q hQ1 N h j k hjk, if_neg hjk, zero_add]
  have hs2 : ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * (∑ i, h (σ i)) ^ 2
      ≤ N * q + (N : ℝ) ^ 2 * q ^ 2 := by
    have e : ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * (∑ i, h (σ i)) ^ 2
        = ∑ j, ∑ k, ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * (h (σ j) * h (σ k)) := by
      simp_rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
    rw [e]
    calc ∑ j : Fin N, ∑ k : Fin N, ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * (h (σ j) * h (σ k))
        ≤ ∑ j : Fin N, ∑ k : Fin N, ((if j = k then q else 0) + q ^ 2) :=
          Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hterm j k))
      _ = N * q + (N : ℝ) ^ 2 * q ^ 2 := by
          simp [Finset.sum_add_distrib]
          ring
  have hs0 : ∀ σ : Fin N → Pi, 0 ≤ ∑ i, h (σ i) :=
    fun σ => Finset.sum_nonneg (fun i _ => (hh01 _).1)
  have hc0 : 0 ≤ 1 - (K : ℝ) * μ := by linarith
  exact avg_bounds (fun σ : Fin N → Pi => ∏ i, Q (σ i)) (fun σ => ∑ i, h (σ i)) hw0
    (moment0 Q hQ1 N) hs0 N hN q hq0 hs1 hs2 (1 - (K : ℝ) * μ) μ hc0 hμ hNμ

theorem measurable_inv_sp {X : Type*} [MeasurableSpace X] {K : ℕ}
    (Pi : Finset (X → Fin K)) (hPiMeas : ∀ π ∈ Pi, Measurable π) (Q : Pi → ℝ) (μ : ℝ)
    (π : X → Fin K) (hπ : Measurable π) :
    Measurable (fun x => 1 / smoothProj Pi Q μ x (π x)) :=
  measurable_const.div
    (measurable_eval_pair.comp ((measurable_smoothProj Pi hPiMeas Q μ).prodMk hπ))

theorem inv_sp_bounds {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ)
    (hQ0 : ∀ p, 0 ≤ Q p) (μ : ℝ) (hμ : 0 < μ) (hKμ : (K : ℝ) * μ ≤ 1) (x : X) (a : Fin K) :
    0 ≤ 1 / smoothProj Pi Q μ x a ∧ 1 / smoothProj Pi Q μ x a ≤ 1 / μ := by
  have h := sp_ge Pi Q hQ0 μ hKμ x a
  have hpos : 0 < smoothProj Pi Q μ x a := lt_of_lt_of_le hμ h
  exact ⟨by positivity, one_div_le_one_div_of_le hμ h⟩

theorem integrable_inv_sp {X : Type*} [MeasurableSpace X] {K : ℕ}
    (Pi : Finset (X → Fin K)) (hPiMeas : ∀ π ∈ Pi, Measurable π) (ν : Measure X)
    [IsProbabilityMeasure ν] (Q : Pi → ℝ) (hQ0 : ∀ p, 0 ≤ Q p) (μ : ℝ) (hμ : 0 < μ)
    (hKμ : (K : ℝ) * μ ≤ 1) (π : X → Fin K) (hπ : Measurable π) :
    Integrable (fun x => 1 / smoothProj Pi Q μ x (π x)) ν := by
  refine Integrable.mono' (integrable_const (1 / μ))
    (measurable_inv_sp Pi hPiMeas Q μ π hπ).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  obtain ⟨h0, h1⟩ := inv_sp_bounds Pi Q hQ0 μ hμ hKμ x (π x)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1

theorem vpop_sparsify {X : Type*} [MeasurableSpace X] {K : ℕ}
    (Pi : Finset (X → Fin K)) (hPiMeas : ∀ π ∈ Pi, Measurable π) (ν : Measure X)
    [IsProbabilityMeasure ν] (Q : Pi → ℝ) (hQ0 : ∀ p, 0 ≤ Q p) (hQ1 : ∑ p, Q p = 1)
    (π : X → Fin K) (hπ : Measurable π) (μ : ℝ) (hμ : 0 < μ) (hKμ : (K : ℝ) * μ ≤ 1)
    (N : ℕ) (hN : 0 < N) (hNμ : 1 - (K : ℝ) * μ ≤ N * μ) :
    Vpop ν Pi Q π μ ≤ ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * Vpop ν Pi (emp σ) π μ := by
  unfold Vpop
  have hint : ∀ σ : Fin N → Pi, Integrable (fun x => 1 / smoothProj Pi (emp σ) μ x (π x)) ν :=
    fun σ => integrable_inv_sp Pi hPiMeas ν (emp σ) (emp_nonneg σ) μ hμ hKμ π hπ
  calc ∫ x, 1 / smoothProj Pi Q μ x (π x) ∂ν
      ≤ ∫ x, ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * (1 / smoothProj Pi (emp σ) μ x (π x)) ∂ν :=
        integral_mono (integrable_inv_sp Pi hPiMeas ν Q hQ0 μ hμ hKμ π hπ)
          (integrable_finsetSum _ (fun σ _ => (hint σ).const_mul _))
          (fun x => (pointwise_sparsify Pi Q hQ0 hQ1 μ hμ hKμ N hN hNμ x (π x)).1)
    _ = ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * ∫ x, 1 / smoothProj Pi (emp σ) μ x (π x) ∂ν := by
        rw [integral_finsetSum _ (fun σ _ => (hint σ).const_mul _)]
        exact Finset.sum_congr rfl (fun σ _ => integral_const_mul _ _)

theorem vhat_sparsify {X : Type*} {K : ℕ}
    (Pi : Finset (X → Fin K)) (Q : Pi → ℝ) (hQ0 : ∀ p, 0 ≤ Q p) (hQ1 : ∑ p, Q p = 1)
    (π : X → Fin K) (μ : ℝ) (hμ : 0 < μ) (hKμ : (K : ℝ) * μ ≤ 1)
    (N : ℕ) (hN : 0 < N) (hNμ : 1 - (K : ℝ) * μ ≤ N * μ) (xs : ℕ → X) (n : ℕ) :
    ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * Vhat Pi (emp σ) π μ xs n ≤ 2 * Vhat Pi Q π μ xs n := by
  unfold Vhat
  simp_rw [mul_div_assoc', Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  gcongr with i hi
  exact (pointwise_sparsify Pi Q hQ0 hQ1 μ hμ hKμ N hN hNμ (xs i) (π (xs i))).2.trans
    (le_of_eq (by ring))


theorem main_ineq {X : Type*} [MeasurableSpace X] {K : ℕ}
    (Pi : Finset (X → Fin K)) (hPiMeas : ∀ π ∈ Pi, Measurable π) (ν : Measure X)
    [IsProbabilityMeasure ν] (Q : Pi → ℝ) (hQ0 : ∀ p, 0 ≤ Q p) (hQ1 : ∑ p, Q p = 1)
    (π : X → Fin K) (hπ : Measurable π) (μ : ℝ) (hμ : 0 < μ) (hKμ : (K : ℝ) * μ ≤ 1)
    (N : ℕ) (hN : 0 < N) (hNμ : 1 - (K : ℝ) * μ ≤ N * μ) (xs : ℕ → X) (n : ℕ) (R : ℝ)
    (hgood : ∀ σ : Fin N → Pi, Vpop ν Pi (emp σ) π μ ≤ 2 * Vhat Pi (emp σ) π μ xs n + R) :
    Vpop ν Pi Q π μ ≤ 4 * Vhat Pi Q π μ xs n + R := by
  have h1 := vpop_sparsify Pi hPiMeas ν Q hQ0 hQ1 π hπ μ hμ hKμ N hN hNμ
  have h2 := vhat_sparsify Pi Q hQ0 hQ1 π μ hμ hKμ N hN hNμ xs n
  have hw0 : ∀ σ : Fin N → Pi, 0 ≤ ∏ i, Q (σ i) := fun σ => Finset.prod_nonneg (fun i _ => hQ0 _)
  have h3 : ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * Vpop ν Pi (emp σ) π μ
      ≤ ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * (2 * Vhat Pi (emp σ) π μ xs n + R) :=
    Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (hgood σ) (hw0 σ))
  have h4 : ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * (2 * Vhat Pi (emp σ) π μ xs n + R)
      = 2 * ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * Vhat Pi (emp σ) π μ xs n + R := by
    rw [show ∑ σ : Fin N → Pi, (∏ i, Q (σ i)) * (2 * Vhat Pi (emp σ) π μ xs n + R)
        = ∑ σ : Fin N → Pi, (2 * ((∏ i, Q (σ i)) * Vhat Pi (emp σ) π μ xs n)
          + R * ∏ i, Q (σ i)) from Finset.sum_congr rfl (fun σ _ => by ring),
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, moment0 Q hQ1 N]
    ring
  linarith

theorem arith1 (Vh ℓ D c μ n Nn : ℝ) (hVh : 0 ≤ Vh) (hℓ : 0 ≤ ℓ) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (hμ : 0 < μ) (hn : 0 < n) (hN : Nn ≤ c / μ + 3) :
    4 * Vh + 4 * (1 / μ) * (Nn * ℓ + D) / n
      ≤ 64 / 10 * Vh + 75 * c * ℓ / (μ ^ 2 * n) + 63 / 10 * (2 * ℓ + D) / (μ * n) := by
  have e1 : 4 * (1 / μ) * (Nn * ℓ + D) / n = (4 * (Nn * ℓ + D)) * (1 / (μ * n)) := by
    field_simp
  have e2 : 75 * c * ℓ / (μ ^ 2 * n) = (75 * (c / μ) * ℓ) * (1 / (μ * n)) := by
    field_simp
  have e3 : 63 / 10 * (2 * ℓ + D) / (μ * n) = (63 / 10 * (2 * ℓ + D)) * (1 / (μ * n)) := by
    field_simp
  rw [e1, e2, e3]
  have hu : 0 < 1 / (μ * n) := by positivity
  have hcm : 0 ≤ c / μ * ℓ := by positivity
  have hNl := mul_le_mul_of_nonneg_right hN hℓ
  have key : 4 * (Nn * ℓ + D) ≤ 75 * (c / μ) * ℓ + 63 / 10 * (2 * ℓ + D) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right key hu.le]

theorem arith2 (ℓ D c μ n K : ℝ) (hK : 1 ≤ K) (hℓ : 0 ≤ ℓ) (hD : 0 ≤ D) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hμ : 0 < μ) (hn : 0 < n) (hsq : (ℓ + D) / (K * n) ≤ μ ^ 2)
    (h4 : 4 * K * (ℓ + D) ≤ n) :
    75 * c * ℓ / (μ ^ 2 * n) + 63 / 10 * (2 * ℓ + D) / (μ * n) ≤ 813 / 10 * K := by
  have hKn : 0 < K * n := by positivity
  have hL : ℓ + D ≤ μ ^ 2 * (K * n) := by rwa [div_le_iff₀ hKn] at hsq
  have hT1 : 75 * c * ℓ / (μ ^ 2 * n) ≤ 75 * K := by
    rw [div_le_iff₀ (by positivity)]
    have : c * ℓ ≤ ℓ := by nlinarith
    nlinarith
  have hsq2 : 4 * (ℓ + D) ^ 2 ≤ (μ * n) ^ 2 := by
    have h5 : 4 * K * (ℓ + D) * (ℓ + D) ≤ n * (ℓ + D) :=
      mul_le_mul_of_nonneg_right h4 (by positivity)
    have h6 : n * (ℓ + D) ≤ n * (μ ^ 2 * (K * n)) := mul_le_mul_of_nonneg_left hL hn.le
    have hK0 : 0 < K := by linarith
    have : K * (4 * (ℓ + D) ^ 2) ≤ K * (μ * n) ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left this hK0
  have h2L : 2 * (ℓ + D) ≤ μ * n := by
    have h0 : 0 ≤ μ * n := by positivity
    nlinarith [sq_nonneg (2 * (ℓ + D) - μ * n), sq_nonneg (2 * (ℓ + D) + μ * n)]
  have hT2 : 63 / 10 * (2 * ℓ + D) / (μ * n) ≤ 63 / 10 * K := by
    rw [div_le_iff₀ (by positivity)]
    have : 2 * ℓ + D ≤ μ * n := by linarith
    have h0 : 0 ≤ μ * n := by positivity
    nlinarith
  linarith

theorem vhat_nonneg {X : Type*} {K : ℕ} (Pi : Finset (X → Fin K)) (Q : Pi → ℝ)
    (hQ0 : ∀ p, 0 ≤ Q p) (π : X → Fin K) (μ : ℝ) (hμ : 0 < μ) (hKμ : (K : ℝ) * μ ≤ 1)
    (xs : ℕ → X) (n : ℕ) : 0 ≤ Vhat Pi Q π μ xs n := by
  unfold Vhat
  exact div_nonneg (Finset.sum_nonneg (fun i _ =>
    (inv_sp_bounds Pi Q hQ0 μ hμ hKμ (xs i) (π (xs i))).1)) (Nat.cast_nonneg _)

end VDev

open MeasureTheory TamingMonster.Regret in
theorem solution {X : Type*} [MeasurableSpace X] {K : ℕ} [NeZero K]
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (hPiMeas : ∀ π ∈ Pi, Measurable π)
    (ν : Measure X) [IsProbabilityMeasure ν]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (x : ℕ → Ω → X) (hxmeas : ∀ t, Measurable (x t))
    (hxind : ProbabilityTheory.iIndepFun x P) (hxlaw : ∀ t, P.map (x t) = ν)
    (τ : ℕ → ℕ) (hτ0 : τ 0 = 0) (hτ : StrictMono τ)
    (μ : ℕ → ℝ) (hμ : ∀ m, 1 ≤ m → 0 < μ m ∧ μ m ≤ 1 / (K : ℝ))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    P {ω | ¬ ∀ Q : Pi → ℝ, (∀ π, 0 ≤ Q π) → ∑ π, Q π = 1 → ∀ π : Pi, ∀ m : ℕ, 1 ≤ m →
        (Vpop ν Pi Q (π : X → Fin K) (μ m) ≤
            64 / 10 * Vhat Pi Q (π : X → Fin K) (μ m) (fun i => x i ω) (τ m)
            + 75 * (1 - (K : ℝ) * μ m) * Real.log (Pi.card : ℝ) / (μ m ^ 2 * (τ m : ℝ))
            + 63 / 10 * Real.log (2 * (Pi.card : ℝ) ^ 2 * (m : ℝ) ^ 2 / δ) / (μ m * (τ m : ℝ)))
        ∧ (Real.sqrt (Real.log (2 * (Pi.card : ℝ) * (m : ℝ) ^ 2 / δ) / ((K : ℝ) * (τ m : ℝ)))
              ≤ μ m →
            4 * (K : ℝ) * Real.log (2 * (Pi.card : ℝ) * (m : ℝ) ^ 2 / δ) ≤ (τ m : ℝ) →
            Vpop ν Pi Q (π : X → Fin K) (μ m) ≤
              64 / 10 * Vhat Pi Q (π : X → Fin K) (μ m) (fun i => x i ω) (τ m)
              + 813 / 10 * (K : ℝ))} ≤ ENNReal.ofReal δ := by
  classical
  have hcard1 : (1 : ℝ) ≤ (Pi.card : ℝ) := by exact_mod_cast hPi.card_pos
  have hℓ0 : 0 ≤ Real.log (Pi.card : ℝ) := Real.log_nonneg hcard1
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
  have hK0 : (0 : ℝ) < K := by linarith
  have hmu : ∀ k : ℕ, 0 < μ (k + 1) ∧ (K : ℝ) * μ (k + 1) ≤ 1 := by
    intro k
    obtain ⟨h0, h1⟩ := hμ (k + 1) (by omega)
    refine ⟨h0, ?_⟩
    have := mul_le_mul_of_nonneg_left h1 hK0.le
    rwa [mul_one_div_cancel hK0.ne'] at this
  set Nk : ℕ → ℕ := fun k => ⌈(1 - (K : ℝ) * μ (k + 1)) / μ (k + 1)⌉₊ + 1 with hNk
  have hNkpos : ∀ k, 0 < Nk k := fun k => by simp only [hNk]; omega
  have hNkμ : ∀ k, 1 - (K : ℝ) * μ (k + 1) ≤ (Nk k : ℝ) * μ (k + 1) := by
    intro k
    have h0 := (hmu k).1
    have hc := Nat.le_ceil ((1 - (K : ℝ) * μ (k + 1)) / μ (k + 1))
    have : (1 - (K : ℝ) * μ (k + 1)) / μ (k + 1) ≤ (Nk k : ℝ) := by
      simp only [hNk]; push_cast; linarith
    rwa [div_le_iff₀ h0] at this
  have hNkle : ∀ k, ((Nk k : ℝ) + 1) ≤ (1 - (K : ℝ) * μ (k + 1)) / μ (k + 1) + 3 := by
    intro k
    have h0 := (hmu k).1
    have hc0 : 0 ≤ (1 - (K : ℝ) * μ (k + 1)) / μ (k + 1) :=
      div_nonneg (by linarith [(hmu k).2]) h0.le
    have := Nat.ceil_lt_add_one hc0
    simp only [hNk]; push_cast; linarith
  have hnk : ∀ k, 1 ≤ τ (k + 1) := fun k => by
    have := hτ (show 0 < k + 1 by omega); omega
  set dk : ℕ → ℝ := fun k =>
    δ / (2 * (Pi.card : ℝ) ^ (Nk k + 1) * ((k : ℝ) + 1) ^ 2) with hdk
  have hdk0 : ∀ k, 0 < dk k := fun k => by simp only [hdk]; positivity
  set bad : (k : ℕ) → (Fin (Nk k) → Pi) → Pi → Set Ω := fun k σ π =>
    {ω | ¬ (Vpop ν Pi (VDev.emp σ) (π : X → Fin K) (μ (k + 1)) ≤
      2 * Vhat Pi (VDev.emp σ) (π : X → Fin K) (μ (k + 1)) (fun i => x i ω) (τ (k + 1))
      + 4 * (1 / μ (k + 1)) * Real.log (1 / dk k) / (τ (k + 1)))} with hbad
  have hbadP : ∀ k σ π, P (bad k σ π) ≤ ENNReal.ofReal (dk k) := fun k σ π =>
    VDev.chernoff_lower P ν x hxmeas hxind hxlaw
      (fun y => 1 / smoothProj Pi (VDev.emp σ) (μ (k + 1)) y ((π : X → Fin K) y))
      (VDev.measurable_inv_sp Pi hPiMeas (VDev.emp σ) (μ (k + 1)) (π : X → Fin K) (hPiMeas π π.2))
      (1 / μ (k + 1)) (by have := (hmu k).1; positivity)
      (fun y => (VDev.inv_sp_bounds Pi (VDev.emp σ) (VDev.emp_nonneg σ) _ (hmu k).1 (hmu k).2
        y _).1)
      (fun y => (VDev.inv_sp_bounds Pi (VDev.emp σ) (VDev.emp_nonneg σ) _ (hmu k).1 (hmu k).2
        y _).2)
      (τ (k + 1)) (hnk k) (dk k) (hdk0 k)
  set Bad : Set Ω := ⋃ k, ⋃ σ : Fin (Nk k) → Pi, ⋃ π : Pi, bad k σ π with hBad
  -- the zeta sum
  have hz : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h1 := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    rw [Finset.sum_range_one] at h1
    norm_num at h1
    simpa only [one_div] using h1
  have hz2 : HasSum (fun k : ℕ => δ / 2 * (1 / ((k : ℝ) + 1) ^ 2)) (δ / 2 * (Real.pi ^ 2 / 6)) :=
    hz.mul_left _
  have hBadP : P Bad ≤ ENNReal.ofReal δ := by
    calc P Bad ≤ ∑' k, P (⋃ σ : Fin (Nk k) → Pi, ⋃ π : Pi, bad k σ π) := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (δ / 2 * (1 / ((k : ℝ) + 1) ^ 2)) := by
          refine ENNReal.tsum_le_tsum (fun k => ?_)
          calc P (⋃ σ : Fin (Nk k) → Pi, ⋃ π : Pi, bad k σ π)
              ≤ ∑ σ : Fin (Nk k) → Pi, P (⋃ π : Pi, bad k σ π) := measure_iUnion_fintype_le _ _
            _ ≤ ∑ σ : Fin (Nk k) → Pi, ∑ π : Pi, P (bad k σ π) :=
                Finset.sum_le_sum (fun σ _ => measure_iUnion_fintype_le _ _)
            _ ≤ ∑ σ : Fin (Nk k) → Pi, ∑ π : Pi, ENNReal.ofReal (dk k) :=
                Finset.sum_le_sum (fun σ _ => Finset.sum_le_sum (fun π _ => hbadP k σ π))
            _ = ENNReal.ofReal (δ / 2 * (1 / ((k : ℝ) + 1) ^ 2)) := by
                rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
                  Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul,
                  nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
                  ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
                congr 1
                simp only [hdk]
                push_cast
                have : (0 : ℝ) < (Pi.card : ℝ) := by linarith
                field_simp
                ring
      _ = ENNReal.ofReal (∑' k : ℕ, δ / 2 * (1 / ((k : ℝ) + 1) ^ 2)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hz2.summable).symm
      _ ≤ ENNReal.ofReal δ := by
          apply ENNReal.ofReal_le_ofReal
          rw [hz2.tsum_eq]
          have hpi := Real.pi_lt_d2
          have hpi0 := Real.pi_pos
          have h12 : Real.pi ^ 2 ≤ 12 := by nlinarith
          calc δ / 2 * (Real.pi ^ 2 / 6) = δ * Real.pi ^ 2 / 12 := by ring
            _ ≤ δ * 12 / 12 := by gcongr
            _ = δ := by ring
  have hsub : {ω | ¬ ∀ Q : Pi → ℝ, (∀ π, 0 ≤ Q π) → ∑ π, Q π = 1 → ∀ π : Pi, ∀ m : ℕ, 1 ≤ m →
        (Vpop ν Pi Q (π : X → Fin K) (μ m) ≤
            64 / 10 * Vhat Pi Q (π : X → Fin K) (μ m) (fun i => x i ω) (τ m)
            + 75 * (1 - (K : ℝ) * μ m) * Real.log (Pi.card : ℝ) / (μ m ^ 2 * (τ m : ℝ))
            + 63 / 10 * Real.log (2 * (Pi.card : ℝ) ^ 2 * (m : ℝ) ^ 2 / δ) / (μ m * (τ m : ℝ)))
        ∧ (Real.sqrt (Real.log (2 * (Pi.card : ℝ) * (m : ℝ) ^ 2 / δ) / ((K : ℝ) * (τ m : ℝ)))
              ≤ μ m →
            4 * (K : ℝ) * Real.log (2 * (Pi.card : ℝ) * (m : ℝ) ^ 2 / δ) ≤ (τ m : ℝ) →
            Vpop ν Pi Q (π : X → Fin K) (μ m) ≤
              64 / 10 * Vhat Pi Q (π : X → Fin K) (μ m) (fun i => x i ω) (τ m)
              + 813 / 10 * (K : ℝ))} ⊆ Bad := by
    intro ω hω
    by_contra hnot
    apply hω
    intro Q hQ0 hQ1 π m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hgood : ∀ σ : Fin (Nk k) → Pi,
        Vpop ν Pi (VDev.emp σ) (π : X → Fin K) (μ (k + 1)) ≤
          2 * Vhat Pi (VDev.emp σ) (π : X → Fin K) (μ (k + 1)) (fun i => x i ω) (τ (k + 1))
          + 4 * (1 / μ (k + 1)) * Real.log (1 / dk k) / (τ (k + 1)) := by
      intro σ
      by_contra h
      exact hnot (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨π, h⟩⟩⟩)
    have hmain := VDev.main_ineq Pi hPiMeas ν Q hQ0 hQ1 (π : X → Fin K) (hPiMeas π π.2)
      (μ (k + 1)) (hmu k).1 (hmu k).2 (Nk k) (hNkpos k) (hNkμ k) (fun i => x i ω) (τ (k + 1))
      _ hgood
    -- logarithms
    set ℓ := Real.log (Pi.card : ℝ) with hℓ
    set D := Real.log 2 + 2 * Real.log ((k : ℝ) + 1) - Real.log δ with hD
    have hD0 : 0 ≤ D := by
      have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h2 : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
      have h3 : Real.log δ < 0 := Real.log_neg hδ0 hδ1
      simp only [hD]; linarith
    have hcpos : (0 : ℝ) < (Pi.card : ℝ) := by linarith
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hlogd : Real.log (1 / dk k) = ((Nk k : ℝ) + 1) * ℓ + D := by
      simp only [hdk, hD, hℓ]
      rw [one_div_div, Real.log_div (by positivity) hδ0.ne', Real.log_mul (by positivity)
        (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow,
        Real.log_pow]
      push_cast
      ring
    have hL2 : Real.log (2 * (Pi.card : ℝ) ^ 2 * (((k + 1 : ℕ)) : ℝ) ^ 2 / δ) = 2 * ℓ + D := by
      simp only [hD, hℓ]
      push_cast
      rw [Real.log_div (by positivity) hδ0.ne', Real.log_mul (by positivity)
        (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow,
        Real.log_pow]
      push_cast
      ring
    have hL1 : Real.log (2 * (Pi.card : ℝ) * (((k + 1 : ℕ)) : ℝ) ^ 2 / δ) = ℓ + D := by
      simp only [hD, hℓ]
      push_cast
      rw [Real.log_div (by positivity) hδ0.ne', Real.log_mul (by positivity)
        (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast
      ring
    rw [hlogd] at hmain
    have hVh := VDev.vhat_nonneg Pi Q hQ0 (π : X → Fin K) (μ (k + 1)) (hmu k).1 (hmu k).2
      (fun i => x i ω) (τ (k + 1))
    have hnR : (0 : ℝ) < (τ (k + 1) : ℝ) := by exact_mod_cast hnk k
    have hc0 : 0 ≤ 1 - (K : ℝ) * μ (k + 1) := by linarith [(hmu k).2]
    have hfirst := VDev.arith1 (Vhat Pi Q (π : X → Fin K) (μ (k + 1)) (fun i => x i ω) (τ (k + 1)))
      ℓ D (1 - (K : ℝ) * μ (k + 1)) (μ (k + 1)) (τ (k + 1)) ((Nk k : ℝ) + 1) hVh hℓ0 hD0 hc0
      (hmu k).1 hnR (hNkle k)
    rw [hL2, hL1]
    refine ⟨by linarith, fun hs h4 => ?_⟩
    have hsq : (ℓ + D) / ((K : ℝ) * (τ (k + 1) : ℝ)) ≤ μ (k + 1) ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
      rwa [Real.sq_sqrt (div_nonneg (by linarith) (by positivity))] at this
    have hsecond := VDev.arith2 ℓ D (1 - (K : ℝ) * μ (k + 1)) (μ (k + 1)) (τ (k + 1)) K hK1 hℓ0
      hD0 hc0 (by linarith [mul_nonneg hK0.le (hmu k).1.le]) (hmu k).1 hnR hsq h4
    linarith
  exact (measure_mono hsub).trans hBadP
