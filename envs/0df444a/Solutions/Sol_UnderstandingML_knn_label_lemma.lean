-- Prove2me | solution 1 for UnderstandingML.knn_label_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T07:54:36.61507+00:00
-- url     : https://prove2.me/submissions/cea45392-e478-4fe5-b958-3d4c6464244b

import Definitions.Def_UnderstandingML_NearestNeighbor
import Mathlib

open MeasureTheory

namespace KnnLabel

/-- The analytic core: `log t + (n-1) log (1-t) + n t ≤ log (1/√n)` for `n ≥ 4`, `t ∈ (0,1)`. -/
lemma key_analytic (n : ℝ) (hn : 4 ≤ n) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    Real.log t + (n - 1) * Real.log (1 - t) + n * t ≤ Real.log (1 / Real.sqrt n) := by
  set u := 1 / Real.sqrt n with hu_def
  have hsn : 2 ≤ Real.sqrt n := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hn
  have hu0 : 0 < u := by positivity
  have hu2 : u ≤ 1 / 2 := by
    rw [hu_def]; exact one_div_le_one_div_of_le (by norm_num) hsn
  have hnu : n * u ^ 2 = 1 := by
    rw [hu_def, div_pow, Real.sq_sqrt (by linarith)]; field_simp
  have hn_eq : n = 1 / u ^ 2 := by field_simp; linarith
  have h1 : Real.log t ≤ Real.log u + t / u - 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos ht0 hu0)
    rw [Real.log_div ht0.ne' hu0.ne'] at this; linarith
  have h2 : Real.log (1 - t) ≤ Real.log (1 - u) + (u - t) / (1 - u) := by
    have hu1 : 0 < 1 - u := by linarith
    have := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < 1 - t) hu1)
    rw [Real.log_div (by linarith) hu1.ne'] at this
    have e : (1 - t) / (1 - u) - 1 = (u - t) / (1 - u) := by field_simp; ring
    linarith
  have h3 : Real.log (1 - u) ≤ -(2 * u / (2 - u)) := by
    have hu1 : 0 < 1 - u := by linarith
    have := Real.le_log_one_add_of_nonneg (x := u / (1 - u)) (by positivity)
    have e1 : 1 + u / (1 - u) = (1 - u)⁻¹ := by field_simp; ring
    have hu2' : (2 - u) ≠ 0 := by intro h; linarith
    have e2 : 2 * (u / (1 - u)) / (u / (1 - u) + 2) = 2 * u / (2 - u) := by
      have h3 : u / (1 - u) + 2 = (2 - u) / (1 - u) := by field_simp; ring
      rw [h3, ← mul_div_assoc, div_div_div_cancel_right₀ hu1.ne']
    rw [e1, Real.log_inv, e2] at this; linarith
  have hn1 : 0 ≤ n - 1 := by linarith
  have hB : (n - 1) * Real.log (1 - t) ≤ (n - 1) * (-(2 * u / (2 - u)) + (u - t) / (1 - u)) := by
    apply mul_le_mul_of_nonneg_left _ hn1; linarith
  have hfinal : t / u - 1 + (n - 1) * (-(2 * u / (2 - u)) + (u - t) / (1 - u)) + n * t =
      (2 * u - 1) / (2 - u) := by
    rw [hn_eq]
    have hu1 : (1 - u) ≠ 0 := by intro h; linarith
    have hu2' : (2 - u) ≠ 0 := by intro h; linarith
    field_simp
    ring
  have hneg : (2 * u - 1) / (2 - u) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  linarith

/-- Weight of a label vector. -/
def W {k : ℕ} (p : Fin k → ℝ) (Z : Fin k → Bool) : ℝ := ∏ i, (if Z i then p i else 1 - p i)

/-- Number of ones. -/
def cnt {k : ℕ} (Z : Fin k → Bool) : ℝ := ∑ i, if Z i then (1 : ℝ) else 0

lemma W_nonneg {k : ℕ} {p : Fin k → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (Z : Fin k → Bool) :
    0 ≤ W p Z :=
  Finset.prod_nonneg (fun i _ ↦ by
    have := hp i; split_ifs <;> linarith [this.1, this.2])

lemma sum_W {k : ℕ} (p : Fin k → ℝ) : ∑ Z, W p Z = 1 := by
  unfold W
  have h := Fintype.prod_sum (fun (i : Fin k) (b : Bool) ↦ if b then p i else 1 - p i)
  rw [← h]
  simp

lemma sum_W_cnt {k : ℕ} (p : Fin k → ℝ) : ∑ Z, W p Z * cnt Z = ∑ i, p i := by
  unfold cnt
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; funext j
  have key : ∀ Z : Fin k → Bool, W p Z * (if Z j then (1 : ℝ) else 0) =
      ∏ i, ((if Z i then p i else 1 - p i) * (if i = j then (if Z i then 1 else 0) else 1)) := by
    intro Z
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j]
    simp [W]
  simp_rw [key]
  have h := Fintype.prod_sum (fun (i : Fin k) (b : Bool) ↦ (if b then p i else 1 - p i) *
    (if i = j then (if b then (1 : ℝ) else 0) else 1))
  rw [← h, Finset.prod_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · simp

/-- Chernoff's bound for sums of independent (non-identical) Bernoulli variables. -/
lemma chernoff {k : ℕ} {p : Fin k → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∑ Z, W p Z * (if (k : ℝ) / 2 ≤ cnt Z then 1 else 0) ≤
      Real.exp (-τ * k / 2 + (∑ i, p i) * (Real.exp τ - 1)) := by
  calc ∑ Z, W p Z * (if (k : ℝ) / 2 ≤ cnt Z then 1 else 0)
      ≤ ∑ Z, W p Z * Real.exp (τ * (cnt Z - k / 2)) := by
        apply Finset.sum_le_sum; intro Z _
        apply mul_le_mul_of_nonneg_left _ (W_nonneg hp Z)
        split_ifs with h
        · exact Real.one_le_exp (mul_nonneg hτ (by linarith))
        · exact (Real.exp_pos _).le
    _ = Real.exp (-τ * k / 2) * ∏ i, (1 - p i + p i * Real.exp τ) := by
        have e : ∀ Z : Fin k → Bool, W p Z * Real.exp (τ * (cnt Z - k / 2)) =
            Real.exp (-τ * k / 2) * ∏ i, ((if Z i then p i else 1 - p i) *
              (if Z i then Real.exp τ else 1)) := by
          intro Z
          rw [Finset.prod_mul_distrib, W]
          have : Real.exp (τ * (cnt Z - k / 2)) = Real.exp (-τ * k / 2) *
              ∏ i, (if Z i then Real.exp τ else 1) := by
            have hsplit : τ * (cnt Z - k / 2) = -τ * k / 2 + ∑ i, (if Z i then τ else 0) := by
              unfold cnt
              rw [mul_sub, Finset.mul_sum]
              simp only [mul_ite, mul_one, mul_zero]
              ring
            rw [hsplit, Real.exp_add, Real.exp_sum]
            congr 1; apply Finset.prod_congr rfl; intro i _; split_ifs <;> simp
          rw [this]; ring
        simp_rw [e]
        have h := Fintype.prod_sum (fun (i : Fin k) (b : Bool) ↦ (if b then p i else 1 - p i) *
          (if b then Real.exp τ else 1))
        rw [← Finset.mul_sum, ← h]
        congr 1; apply Finset.prod_congr rfl; intro i _
        simp; ring
    _ ≤ Real.exp (-τ * k / 2) * ∏ i, Real.exp (p i * (Real.exp τ - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply Finset.prod_le_prod
        · intro i _
          have h1 := hp i
          have h2 := mul_nonneg h1.1 (Real.exp_pos τ).le
          linarith [h1.2]
        · intro i _
          have := Real.add_one_le_exp (p i * (Real.exp τ - 1))
          linarith
    _ = _ := by
        rw [← Real.exp_sum, ← Real.exp_add, Finset.sum_mul]


lemma sqrt_eight_div (k : ℕ) (hk : 0 < k) : Real.sqrt (8 / k) = 2 / Real.sqrt ((k : ℝ) / 2) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [show (8 : ℝ) / k = 4 / ((k : ℝ) / 2) by field_simp; norm_num, Real.sqrt_div (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The tail estimate: `(1 - 2P) · P[#ones ≥ k/2] ≤ √(8/k) · P` when the mean `P ≤ 1/2`. -/
lemma tail_bound {k : ℕ} (hk : 10 ≤ k) {p : Fin k → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hP : (∑ i, p i) / k ≤ 1 / 2) :
    (1 - 2 * ((∑ i, p i) / k)) * ∑ Z, W p Z * (if (k : ℝ) / 2 ≤ cnt Z then 1 else 0) ≤
      Real.sqrt (8 / k) * ((∑ i, p i) / k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set P := (∑ i, p i) / k with hPdef
  have hsum : ∑ i, p i = k * P := by rw [hPdef]; field_simp
  have hP0 : 0 ≤ P := div_nonneg (Finset.sum_nonneg (fun i _ ↦ (hp i).1)) hk'.le
  set Q := ∑ Z, W p Z * (if (k : ℝ) / 2 ≤ cnt Z then 1 else 0) with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun Z _ ↦ mul_nonneg (W_nonneg hp Z) (by split_ifs <;> norm_num))
  have ht0 : 0 ≤ 1 - 2 * P := by linarith
  rcases eq_or_lt_of_le hP0 with hPz | hPpos
  · -- Markov
    have hmarkov : Q ≤ 2 * P := by
      calc Q ≤ ∑ Z, W p Z * (cnt Z / ((k : ℝ) / 2)) := by
            apply Finset.sum_le_sum; intro Z _
            apply mul_le_mul_of_nonneg_left _ (W_nonneg hp Z)
            split_ifs with h
            · rw [le_div_iff₀ (by positivity)]; linarith
            · exact div_nonneg (Finset.sum_nonneg (fun i _ ↦ by split_ifs <;> norm_num))
                (by positivity)
        _ = (∑ Z, W p Z * cnt Z) / ((k : ℝ) / 2) := by
            rw [Finset.sum_div]; congr 1; funext Z; ring
        _ = 2 * P := by rw [sum_W_cnt, hsum]; field_simp
    rw [← hPz] at hmarkov ⊢
    have : Q ≤ 0 := by linarith
    nlinarith
  rcases eq_or_lt_of_le hP with hPh | hPlt
  · rw [hPh]; norm_num; positivity
  -- Chernoff at `e^τ = 1/(2P)`
  set τ := Real.log (1 / (2 * P)) with hτ
  have h2P : 0 < 2 * P := by linarith
  have hτ0 : 0 ≤ τ := Real.log_nonneg (by rw [le_div_iff₀ h2P]; linarith)
  have hch := chernoff hp τ hτ0
  have hexpτ : Real.exp τ = 1 / (2 * P) := Real.exp_log (by positivity)
  set n : ℝ := (k : ℝ) / 2 with hn
  set t : ℝ := 1 - 2 * P with ht
  have hexp_eq : -τ * k / 2 + (∑ i, p i) * (Real.exp τ - 1) = n * Real.log (1 - t) + n * t := by
    rw [hexpτ, hsum, hτ, one_div, Real.log_inv, ht, hn]
    field_simp
    ring
  rw [hexp_eq] at hch
  have htpos : 0 < t := by rw [ht]; linarith
  have ht1 : t < 1 := by rw [ht]; linarith
  have hn4 : 4 ≤ n := by
    rw [hn]; have : (10 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hkey := key_analytic n hn4 t htpos ht1
  have h1t : 0 < 1 - t := by linarith
  calc t * Q ≤ t * Real.exp (n * Real.log (1 - t) + n * t) :=
        mul_le_mul_of_nonneg_left hch htpos.le
    _ = Real.exp (Real.log t + n * Real.log (1 - t) + n * t) := by
        rw [add_assoc, Real.exp_add (Real.log t) _, Real.exp_log htpos]
    _ ≤ Real.exp (Real.log (1 - t) + Real.log (1 / Real.sqrt n)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = (1 - t) / Real.sqrt n := by
        rw [Real.exp_add, Real.exp_log h1t, Real.exp_log (by positivity)]; ring
    _ = Real.sqrt (8 / k) * P := by
        rw [sqrt_eight_div k (by omega), ← hn, ht]; ring

end KnnLabel

open UnderstandingML KnnLabel in
theorem solution (k : ℕ) (hk : 10 ≤ k) (p : Fin k → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    ∫ Z, bernoulliErr ((∑ i, p i) / k) (majority Z) ∂(Measure.pi (fun i ↦ bernoulliLaw (p i))) ≤
      (1 + Real.sqrt (8 / k)) * bernoulliErr ((∑ i, p i) / k) (decide (1 / 2 < (∑ i, p i) / k)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set P := (∑ i, p i) / k with hPdef
  -- the Bernoulli laws are probability measures
  have hbern : ∀ q : ℝ, q ∈ Set.Icc (0 : ℝ) 1 → IsProbabilityMeasure (bernoulliLaw q) := by
    intro q hq
    constructor
    simp only [bernoulliLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
      mul_one]
    rw [← ENNReal.ofReal_add hq.1 (by linarith [hq.2])]; simp
  have : ∀ i, IsProbabilityMeasure (bernoulliLaw (p i)) := fun i ↦ hbern _ (hp i)
  have hsing : ∀ q : ℝ, q ∈ Set.Icc (0 : ℝ) 1 → ∀ b : Bool,
      (bernoulliLaw q).real {b} = if b then q else 1 - q := by
    intro q hq b
    rw [measureReal_def]
    cases b <;> simp [bernoulliLaw, ENNReal.toReal_ofReal hq.1,
      ENNReal.toReal_ofReal (by linarith [hq.2] : (0 : ℝ) ≤ 1 - q)]
  -- the integral as a finite sum
  have hint : ∫ Z, bernoulliErr P (majority Z) ∂(Measure.pi (fun i ↦ bernoulliLaw (p i))) =
      ∑ Z, W p Z * bernoulliErr P (decide ((k : ℝ) / 2 < cnt Z)) := by
    rw [integral_fintype Integrable.of_finite]
    congr 1; funext Z
    rw [smul_eq_mul, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    congr 1
    · apply Finset.prod_congr rfl; intro i _
      rw [← measureReal_def, hsing _ (hp i)]
    · simp [majority, cnt]
  rw [hint]
  have hsplit : ∀ Z, W p Z * bernoulliErr P (decide ((k : ℝ) / 2 < cnt Z)) =
      W p Z * P + (1 - 2 * P) * (W p Z * (if (k : ℝ) / 2 < cnt Z then 1 else 0)) := by
    intro Z; unfold bernoulliErr; split_ifs with h1 h2 <;> simp_all <;> ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_W, one_mul, ← Finset.mul_sum]
  by_cases hhalf : 1 / 2 < P
  · -- flip the labels
    simp only [hhalf, decide_true, bernoulliErr, if_true]
    let p' : Fin k → ℝ := fun i ↦ 1 - p i
    have hp' : ∀ i, p' i ∈ Set.Icc (0 : ℝ) 1 := fun i ↦
      ⟨by linarith [(hp i).2], by linarith [(hp i).1]⟩
    have hP' : (∑ i, p' i) / k = 1 - P := by
      simp only [p', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      rw [hPdef]; field_simp
    have htb := tail_bound hk hp' (by rw [hP']; linarith)
    rw [hP'] at htb
    let σ : (Fin k → Bool) ≃ (Fin k → Bool) :=
      { toFun := fun Z i ↦ !Z i, invFun := fun Z i ↦ !Z i,
        left_inv := fun Z ↦ by funext i; simp, right_inv := fun Z ↦ by funext i; simp }
    have hW : ∀ Z, W p' (σ Z) = W p Z := by
      intro Z; unfold W; apply Finset.prod_congr rfl; intro i _
      simp only [σ, Equiv.coe_fn_mk, p']
      by_cases h : Z i = true <;> simp [h]
    have hcnt : ∀ Z, cnt (σ Z) = k - cnt Z := by
      intro Z; unfold cnt
      rw [show (k : ℝ) = ∑ _i : Fin k, (1 : ℝ) by simp, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      simp only [σ, Equiv.coe_fn_mk]
      by_cases h : Z i = true <;> simp [h]
    have hflip : ∑ Z, W p' Z * (if (k : ℝ) / 2 ≤ cnt Z then 1 else 0) =
        1 - ∑ Z, W p Z * (if (k : ℝ) / 2 < cnt Z then 1 else 0) := by
      rw [← Equiv.sum_comp σ]
      simp_rw [hW, hcnt]
      rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
      conv_rhs => rw [← sum_W p]
      apply Finset.sum_congr rfl; intro Z _
      split_ifs with h1 h2 h2 <;> first | (exfalso; linarith) | ring
    rw [hflip] at htb
    have hs8 : 0 ≤ Real.sqrt (8 / k) := Real.sqrt_nonneg _
    nlinarith [htb]
  · simp only [hhalf, decide_false, bernoulliErr, Bool.false_eq_true, if_false]
    push Not at hhalf
    have htb := tail_bound hk hp hhalf
    have hle : ∑ Z, W p Z * (if (k : ℝ) / 2 < cnt Z then 1 else 0) ≤
        ∑ Z, W p Z * (if (k : ℝ) / 2 ≤ cnt Z then 1 else 0) := by
      apply Finset.sum_le_sum; intro Z _
      apply mul_le_mul_of_nonneg_left _ (W_nonneg hp Z)
      split_ifs with h1 h2 <;> first | (exfalso; linarith) | norm_num
    have ht0 : 0 ≤ 1 - 2 * P := by linarith
    have := mul_le_mul_of_nonneg_left hle ht0
    nlinarith [htb]
