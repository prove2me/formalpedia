-- Prove2me | solution 1 for SpectrumLB.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:10:55.905597+00:00
-- url     : https://prove2.me/submissions/d4cc8c6f-fedd-4d1d-bbd3-2289948880d1

import Mathlib

noncomputable def gq (x : ℝ) : ℝ := (Real.exp x - 1) / (Real.exp x + 1)

lemma gq_hasDeriv (x : ℝ) : HasDerivAt gq (2 * Real.exp x / (Real.exp x + 1) ^ 2) x := by
  have h1 : Real.exp x + 1 ≠ 0 := by positivity
  have := ((Real.hasDerivAt_exp x).sub_const 1).div ((Real.hasDerivAt_exp x).add_const 1) h1
  refine this.congr_deriv ?_
  field_simp; ring

lemma gq_lip (x y : ℝ) : |gq x - gq y| ≤ |x - y| / 2 := by
  have hd : ∀ z, HasDerivAt gq (2 * Real.exp z / (Real.exp z + 1) ^ 2) z := gq_hasDeriv
  have hdiff : Differentiable ℝ gq := fun z => (hd z).differentiableAt
  have hbound : ∀ z, ‖deriv gq z‖₊ ≤ (1/2 : NNReal) := by
    intro z
    rw [(hd z).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Real.exp z - 1), Real.exp_pos z]
  have hL := lipschitzWith_of_nnnorm_deriv_le hdiff hbound
  have := hL.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq] at this
  push_cast at this
  linarith

lemma gq_abs (x : ℝ) : |gq x| ≤ 1 := by
  rw [gq, abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.exp x + 1), div_le_one (by positivity),
    abs_le]
  constructor <;> linarith [Real.exp_pos x]

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (p q : Ω → ℝ),
      (∀ y, 0 ≤ p y) → (∀ y, 0 ≤ q y) → ∑ y, p y = 1 → ∑ y, q y = 1 →
      ∀ G : Finset Ω, (∀ y ∈ G, 0 < p y ∧ 0 < q y) → ∀ lam : ℝ,
        ∑ y, (p y + q y) / 2 * ((q y - p y) / (q y + p y)) ^ 2 ≤
          C * (∑ y ∈ Gᶜ, (p y + q y) / 2 +
            ∑ y ∈ G, (p y + q y) / 2 * (Real.log (q y / p y) - lam) ^ 2) := by
  refine ⟨5, by norm_num, ?_⟩
  intro Ω _ _ p q hp hq hsp hsq G hG lam
  set m : Ω → ℝ := fun y => (p y + q y) / 2 with hm
  set δ : Ω → ℝ := fun y => (q y - p y) / (q y + p y) with hδ
  have hm0 : ∀ y, 0 ≤ m y := fun y => by simp only [hm]; linarith [hp y, hq y]
  have hδ1 : ∀ y, δ y ^ 2 ≤ 1 := by
    intro y
    simp only [hδ]
    rcases (add_nonneg (hq y) (hp y)).eq_or_lt with h0 | hpos
    · rw [← h0, div_zero]; norm_num
    · rw [div_pow, div_le_one (by positivity)]
      nlinarith [hp y, hq y]
  have hmδ : ∀ y, m y * δ y = (q y - p y) / 2 := by
    intro y
    simp only [hm, hδ]
    rcases (add_nonneg (hq y) (hp y)).eq_or_lt with h0 | hpos
    · have hp0 : p y = 0 := by linarith [hp y, hq y]
      have hq0 : q y = 0 := by linarith [hp y, hq y]
      rw [hp0, hq0]; ring
    · field_simp; ring
  have hF1 : ∑ y, m y * δ y = 0 := by
    simp_rw [hmδ]; rw [← Finset.sum_div, Finset.sum_sub_distrib, hsq, hsp]; ring
  set t := gq lam with ht
  have ht1 : |t| ≤ 1 := gq_abs lam
  have hF2 : ∀ y ∈ G, (δ y - t) ^ 2 ≤ (Real.log (q y / p y) - lam) ^ 2 / 4 := by
    intro y hy
    obtain ⟨hpy, hqy⟩ := hG y hy
    have hδg : δ y = gq (Real.log (q y / p y)) := by
      simp only [hδ, gq]
      rw [Real.exp_log (by positivity)]
      field_simp
    rw [hδg]
    have := gq_lip (Real.log (q y / p y)) lam
    have h2 : (gq (Real.log (q y / p y)) - t) ^ 2 ≤ ((Real.log (q y / p y) - lam) / 2) ^ 2 := by
      rw [← sq_abs, ← sq_abs ((Real.log (q y / p y) - lam) / 2)]
      apply pow_le_pow_left₀ (abs_nonneg _)
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]; exact this
    rw [div_pow] at h2; norm_num at h2; linarith
  set B := ∑ y ∈ Gᶜ, m y with hB
  set M := ∑ y ∈ G, m y with hM
  set W := ∑ y ∈ G, m y * (δ y - t) ^ 2 with hW
  set V := ∑ y ∈ G, m y * (Real.log (q y / p y) - lam) ^ 2 with hV
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun y _ => hm0 y)
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun y _ => mul_nonneg (hm0 y) (sq_nonneg _))
  have hWV : W ≤ V / 4 := by
    rw [hW, hV, Finset.sum_div]
    apply Finset.sum_le_sum; intro y hy
    have := mul_le_mul_of_nonneg_left (hF2 y hy) (hm0 y)
    linarith
  -- |Σ_G m δ| ≤ B
  have hsplit := Finset.sum_add_sum_compl G (fun y => m y * δ y)
  rw [hF1] at hsplit
  have hcompl_abs : |∑ y ∈ Gᶜ, m y * δ y| ≤ B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun y _ => ?_))
    rw [abs_mul, abs_of_nonneg (hm0 y)]
    have : |δ y| ≤ 1 := by
      have := hδ1 y; rw [← sq_abs] at this; nlinarith [abs_nonneg (δ y)]
    nlinarith [hm0 y]
  have hSG : t * ∑ y ∈ G, m y * δ y ≤ B := by
    have h1 : ∑ y ∈ G, m y * δ y = -∑ y ∈ Gᶜ, m y * δ y := by linarith
    rw [h1]
    calc t * -∑ y ∈ Gᶜ, m y * δ y ≤ |t| * |∑ y ∈ Gᶜ, m y * δ y| := by
          rw [← abs_neg (∑ y ∈ Gᶜ, m y * δ y), ← abs_mul]; exact le_abs_self _
      _ ≤ 1 * B := mul_le_mul ht1 hcompl_abs (abs_nonneg _) zero_le_one
      _ = B := one_mul B
  have htM : t ^ 2 * M ≤ 2 * B + W := by
    have hdecomp : ∑ y ∈ G, m y * δ y = t * M + ∑ y ∈ G, m y * (δ y - t) := by
      rw [hM, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro y _; ring
    have hamgm : ∑ y ∈ G, m y * (-(t * (δ y - t))) ≤ t ^ 2 / 2 * M + W / 2 := by
      rw [hM, hW, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro y _
      have := mul_le_mul_of_nonneg_left
        (show -(t * (δ y - t)) ≤ t ^ 2 / 2 + (δ y - t) ^ 2 / 2 by nlinarith [sq_nonneg (t + (δ y - t))])
        (hm0 y)
      nlinarith
    have hneg : t * ∑ y ∈ G, m y * (δ y - t) = -∑ y ∈ G, m y * (-(t * (δ y - t))) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro y _; ring
    rw [hdecomp, mul_add, hneg] at hSG
    nlinarith
  have hGpart : ∑ y ∈ G, m y * δ y ^ 2 ≤ 2 * W + 2 * (t ^ 2 * M) := by
    rw [hW, hM, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro y _
    have := mul_le_mul_of_nonneg_left
      (show δ y ^ 2 ≤ 2 * (δ y - t) ^ 2 + 2 * t ^ 2 by nlinarith [sq_nonneg (δ y - 2 * t)]) (hm0 y)
    nlinarith
  have hCpart : ∑ y ∈ Gᶜ, m y * δ y ^ 2 ≤ B := by
    apply Finset.sum_le_sum; intro y _
    have := mul_le_mul_of_nonneg_left (hδ1 y) (hm0 y)
    linarith
  have htot : ∑ y, m y * δ y ^ 2 = ∑ y ∈ G, m y * δ y ^ 2 + ∑ y ∈ Gᶜ, m y * δ y ^ 2 :=
    (Finset.sum_add_sum_compl G _).symm
  change ∑ y, m y * δ y ^ 2 ≤ 5 * (B + V)
  rw [htot]
  nlinarith
