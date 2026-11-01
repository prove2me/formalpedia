-- Prove2me | solution 1 for QMCProduct.HalfApprox.definition_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T10:23:46.081299+00:00
-- url     : https://prove2.me/submissions/21bb89bb-bfd4-4e72-a163-db85e0366588

import Definitions.Def_QMCProduct_HalfApprox_Algorithm

set_option autoImplicit false

namespace QMCHyp

open QMCProduct.HalfApprox

/-- the terms of the hypergeometric series, defined by the ratio recursion -/
noncomputable def tm (a b c x : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => tm a b c x n * ((a + n) * (b + n) / ((c + n) * (n + 1))) * x

lemma coef_mul_pow (a b c x : ℝ) (hc : 0 < c) (n : ℕ) :
    ordinaryHypergeometricCoefficient a b c n * x ^ n = tm a b c x n := by
  induction n with
  | zero => simp [ordinaryHypergeometricCoefficient, tm]
  | succ n ih =>
    rw [tm, ← ih]
    simp only [ordinaryHypergeometricCoefficient, ascPochhammer_succ_eval, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_succ, pow_succ]
    have h1 : 0 < (ascPochhammer ℝ n).eval c := ascPochhammer_pos n c hc
    have h2 : (0 : ℝ) < c + n := by positivity
    have h3 : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    field_simp

lemma hyp_eq_tsum (a b c x : ℝ) (hc : 0 < c) :
    ordinaryHypergeometric a b c x = ∑' n, tm a b c x n := by
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  exact tsum_congr (fun n => coef_mul_pow a b c x hc n)

lemma tm_nonneg (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ tm a b c x n := by
  induction n with
  | zero => simp [tm]
  | succ n ih => rw [tm]; positivity

lemma tm_le_pow (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 ≤ x)
    (hratio : ∀ n : ℕ, (a + n) * (b + n) ≤ (c + n) * (n + 1)) (n : ℕ) :
    tm a b c x n ≤ x ^ n := by
  induction n with
  | zero => simp [tm]
  | succ n ih =>
    rw [tm, pow_succ]
    have hr : (a + n) * (b + n) / ((c + n) * (n + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hratio n
    have hr0 : 0 ≤ (a + n) * (b + n) / ((c + n) * (n + 1)) := by positivity
    have h0 := tm_nonneg a b c x ha hb hc hx n
    calc tm a b c x n * ((a + n) * (b + n) / ((c + n) * (n + 1))) * x
        ≤ x ^ n * 1 * x := by gcongr
      _ = x ^ n * x := by ring

lemma tm_summable (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 ≤ x) (hx1 : x < 1)
    (hratio : ∀ n : ℕ, (a + n) * (b + n) ≤ (c + n) * (n + 1)) :
    Summable (tm a b c x) :=
  Summable.of_nonneg_of_le (tm_nonneg a b c x ha hb hc hx) (tm_le_pow a b c x ha hb hc hx hratio)
    (summable_geometric_of_lt_one hx hx1)

lemma hyp_lower (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 ≤ x) (hx1 : x < 1)
    (hratio : ∀ n : ℕ, (a + n) * (b + n) ≤ (c + n) * (n + 1)) (J : ℕ) :
    ∑ n ∈ Finset.range J, tm a b c x n ≤ ordinaryHypergeometric a b c x := by
  rw [hyp_eq_tsum a b c x hc]
  exact (tm_summable a b c x ha hb hc hx hx1 hratio).sum_le_tsum _
    (fun n _ => tm_nonneg a b c x ha hb hc hx n)

lemma hyp_upper (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 ≤ x) (hx1 : x < 1)
    (hratio : ∀ n : ℕ, (a + n) * (b + n) ≤ (c + n) * (n + 1)) (J : ℕ) :
    ordinaryHypergeometric a b c x ≤ ∑ n ∈ Finset.range J, tm a b c x n + x ^ J / (1 - x) := by
  rw [hyp_eq_tsum a b c x hc]
  have hs := tm_summable a b c x ha hb hc hx hx1 hratio
  rw [← hs.sum_add_tsum_nat_add J]
  gcongr
  have hg : Summable (fun n => x ^ (n + J)) :=
    (summable_geometric_of_lt_one hx hx1).comp_injective (add_left_injective J)
  calc ∑' n, tm a b c x (n + J) ≤ ∑' n, x ^ (n + J) :=
        (hs.comp_injective (add_left_injective J)).tsum_le_tsum
          (fun n => tm_le_pow a b c x ha hb hc hx hratio (n + J)) hg
    _ = x ^ J / (1 - x) := by
        simp_rw [pow_add]
        rw [tsum_mul_right, tsum_geometric_of_lt_one hx hx1]
        ring

lemma F3_eq (t : ℝ) :
    F 3 t = 8 / (3 * Real.pi) * t * ordinaryHypergeometric (1 / 2 : ℝ) (1 / 2 : ℝ) (5 / 2 : ℝ) (t ^ 2) := by
  unfold F
  have e1 : (((3 : ℕ) : ℝ) + 1) / 2 = 2 := by norm_num
  have e2 : ((3 : ℕ) : ℝ) / 2 = 1 / 2 + 1 := by norm_num
  have e3 : ((3 : ℕ) : ℝ) / 2 + 1 = 5 / 2 := by norm_num
  rw [e3, e1, e2, Real.Gamma_two, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi.le
  have hs0 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  field_simp
  rw [hs]
  push_cast
  ring

lemma num_lower : (11225 / 10000 : ℝ) ≤ ∑ n ∈ Finset.range 20, tm (1/2) (1/2) (5/2) ((911/1000)^2) n := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tm]
  norm_num

lemma num_upper1 : ∑ n ∈ Finset.range 20, tm (1/2) (1/2) (5/2) ((911/1000)^2) n ≤ (11226 / 10000 : ℝ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tm]
  norm_num

lemma num_upper2 : ∑ n ∈ Finset.range 20, tm (3/2) (3/2) (7/2) ((911/1000)^2) n ≤ (2436 / 1000 : ℝ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tm]
  norm_num

lemma num_tail : ((911/1000 : ℝ)^2) ^ 20 / (1 - (911/1000)^2) ≤ (142 / 1000 : ℝ) := by
  norm_num

lemma ratio1 : ∀ n : ℕ, ((1/2 : ℝ) + n) * (1/2 + n) ≤ (5/2 + n) * (n + 1) := by
  intro n; have : (0 : ℝ) ≤ n := n.cast_nonneg; nlinarith
lemma ratio2 : ∀ n : ℕ, ((3/2 : ℝ) + n) * (3/2 + n) ≤ (7/2 + n) * (n + 1) := by
  intro n; have : (0 : ℝ) ≤ n := n.cast_nonneg; nlinarith

theorem def13 :
    (1 / 3 : ℝ) ≤ 911 / 1000 ∧ (911 / 1000 : ℝ) < 1 ∧
    (∀ v ∈ Set.Ioc (-(1 / 3 : ℝ)) (911 / 1000), hLemma6 v (911 / 1000) < 0) ∧
    (1 / 2 : ℝ) ≤ (1 + F 3 (911 / 1000)) / (1 + 3 * (911 / 1000)) := by
  have hx0 : (0 : ℝ) ≤ (911 / 1000) ^ 2 := by positivity
  have hx1 : ((911 : ℝ) / 1000) ^ 2 < 1 := by norm_num
  have hpi1 := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d4
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro v hv
    unfold hLemma6
    have hH := hyp_upper (1/2) (1/2) (5/2) _ (by norm_num) (by norm_num) (by norm_num) hx0 hx1 ratio1 20
    have hH2 := hyp_upper (3/2) (3/2) (7/2) _ (by norm_num) (by norm_num) (by norm_num) hx0 hx1 ratio2 20
    have u1 := num_upper1
    have u2 := num_upper2
    have ut := num_tail
    apply div_neg_of_neg_of_pos
    · nlinarith
    · have : 0 < 3 * v + 1 := by linarith [hv.1]
      positivity
  · rw [le_div_iff₀ (by norm_num), F3_eq]
    have hL := hyp_lower (1/2) (1/2) (5/2) _ (by norm_num) (by norm_num) (by norm_num) hx0 hx1 ratio1 20
    have l1 := num_lower
    set H := ordinaryHypergeometric (1 / 2 : ℝ) (1 / 2 : ℝ) (5 / 2 : ℝ) ((911 / 1000 : ℝ) ^ 2)
    have hpos : 0 < 3 * Real.pi := by positivity
    have key : 8 / (3 * Real.pi) * (911 / 1000) * H = (8 * (911 / 1000) * H) / (3 * Real.pi) := by ring
    rw [key]
    have : (8665 / 10000 : ℝ) ≤ (8 * (911 / 1000) * H) / (3 * Real.pi) := by
      rw [le_div_iff₀ hpos]; nlinarith
    linarith

end QMCHyp

open QMCProduct.HalfApprox in
theorem solution :
    (1 / 3 : ℝ) ≤ 911 / 1000 ∧ (911 / 1000 : ℝ) < 1 ∧
    (∀ v ∈ Set.Ioc (-(1 / 3 : ℝ)) (911 / 1000), hLemma6 v (911 / 1000) < 0) ∧
    (1 / 2 : ℝ) ≤ (1 + F 3 (911 / 1000)) / (1 + 3 * (911 / 1000)) :=
  QMCHyp.def13
