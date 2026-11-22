-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:02:32.619455+00:00
-- url     : https://prove2.me/submissions/d4a4255a-c8a3-46cb-95b6-cf53a0f8df7e

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OTDLemma25
open Polynomial OptimalTraceDistance.Estimation

/-- the numerator polynomial -/
def pNum (m : ℕ) : Polynomial ℝ := 1 - (Polynomial.Chebyshev.T ℝ m).comp (1 - Polynomial.X)

lemma pNum_natDegree_le (m : ℕ) : (pNum m).natDegree ≤ m := by
  unfold pNum
  refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
  refine natDegree_comp_le.trans ?_
  rw [Polynomial.Chebyshev.natDegree_T]
  have : (1 - X : ℝ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  simpa using Nat.mul_le_mul_left m this

lemma pNum_eval (m : ℕ) (x : ℝ) :
    (pNum m).eval x = 1 - (Polynomial.Chebyshev.T ℝ m).eval (1 - x) := by
  simp [pNum, eval_comp]

lemma pNum_coeff_zero (m : ℕ) : (pNum m).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, pNum_eval]; simp

lemma pNum_coeff_one (m : ℕ) (hm : 1 ≤ m) : (pNum m).coeff 1 = (m : ℝ)^2 := by
  have h := coeff_derivative (pNum m) 0
  simp only [zero_add, Nat.cast_zero, mul_one] at h
  rw [← h, coeff_zero_eq_eval_zero]
  simp only [pNum, derivative_sub, derivative_one, zero_sub, derivative_comp, eval_neg,
    eval_mul, eval_comp, derivative_X, derivative_sub, derivative_one]
  rw [Polynomial.Chebyshev.T_derivative_eq_U]
  simp only [eval_sub, eval_one, eval_X, sub_zero, eval_mul, eval_intCast]
  have : ((m : ℤ) - 1) = ((m - 1 : ℕ) : ℤ) := by omega
  rw [this, Polynomial.Chebyshev.U_eval_one]
  push_cast [hm]
  ring

lemma pNum_eq (m : ℕ) (hm : 1 ≤ m) :
    C ((m : ℝ)^2) * X * rFilter m = pNum m := by
  have hm0 : (m : ℝ)^2 ≠ 0 := by positivity
  conv_rhs => rw [as_sum_range' (pNum m) (m+1) (Nat.lt_succ_of_le (pNum_natDegree_le m))]
  rw [Finset.sum_range_succ', pNum_coeff_zero]
  simp only [rFilter, Finset.mul_sum, map_zero, add_zero]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (1 - (Polynomial.Chebyshev.T ℝ m).comp (1 - X)) = pNum m from rfl,
    ← C_mul_X_pow_eq_monomial]
  have : C ((m:ℝ)^2) * X * (C ((pNum m).coeff (j + 1) / (m:ℝ)^2) * X^j) =
      C ((m:ℝ)^2 * ((pNum m).coeff (j + 1) / (m:ℝ)^2)) * X^(j+1) := by
    rw [C_mul, pow_succ]; ring
  rw [this, mul_div_cancel₀ _ hm0]

lemma rFilter_eval_mul (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    (m : ℝ)^2 * x * (rFilter m).eval x = 1 - (Polynomial.Chebyshev.T ℝ m).eval (1 - x) := by
  have := congrArg (eval x) (pNum_eq m hm)
  simpa [pNum_eval] using this

lemma rFilter_eval_zero (m : ℕ) (hm : 1 ≤ m) : (rFilter m).eval 0 = 1 := by
  have hm0 : (m : ℝ)^2 ≠ 0 := by positivity
  rw [← coeff_zero_eq_eval_zero, rFilter, finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, mul_one, coeff_C_zero]
    rw [show (1 - (Polynomial.Chebyshev.T ℝ m).comp (1 - X)) = pNum m from rfl,
      pNum_coeff_one m hm, div_self hm0]
  · intro j _ hj; rw [coeff_C_mul, coeff_X_pow, if_neg (Ne.symm hj), mul_zero]
  · intro h; simp at h; omega

lemma rFilter_natDegree (m : ℕ) : (rFilter m).natDegree ≤ m - 1 := by
  unfold rFilter
  refine natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)
  refine (natDegree_C_mul_le _ _).trans ?_
  simp at hj; simp; omega

lemma abs_sin_nat_mul_le (u : ℝ) : ∀ n : ℕ, |Real.sin (n * u)| ≤ n * |Real.sin u|
  | 0 => by simp
  | n+1 => by
    have ih := abs_sin_nat_mul_le u n
    have : Real.sin ((n+1 : ℕ) * u) = Real.sin (n*u) * Real.cos u + Real.cos (n*u) * Real.sin u := by
      push_cast; rw [add_mul, one_mul, Real.sin_add]
    rw [this]
    calc |Real.sin (n*u) * Real.cos u + Real.cos (n*u) * Real.sin u|
        ≤ |Real.sin (n*u)| * |Real.cos u| + |Real.cos (n*u)| * |Real.sin u| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |Real.sin (n*u)| * 1 + 1 * |Real.sin u| := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ ≤ ((n+1 : ℕ) : ℝ) * |Real.sin u| := by push_cast; nlinarith


lemma trig_rep (m : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 2) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ Real.pi/2 ∧ x = 2 * Real.sin u ^ 2 ∧
      (Polynomial.Chebyshev.T ℝ m).eval (1 - x) = 1 - 2 * Real.sin (m * u) ^ 2 := by
  set θ := Real.arccos (1 - x) with hθ
  have hc : Real.cos θ = 1 - x := Real.cos_arccos (by linarith) (by linarith)
  refine ⟨θ/2, by linarith [Real.arccos_nonneg (1-x)], by linarith [Real.arccos_le_pi (1-x)], ?_, ?_⟩
  · have h2 : Real.cos θ = Real.cos (2 * (θ/2)) := by ring_nf
    rw [Real.cos_two_mul] at h2
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  · rw [← hc, Polynomial.Chebyshev.T_real_cos]
    have : ((m:ℤ):ℝ) * θ = 2 * (m * (θ/2)) := by push_cast; ring
    rw [this, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (m * (θ/2))]

lemma R_bounds (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 2) :
    0 ≤ (rFilter m).eval x ∧ (rFilter m).eval x ≤ 1 ∧
      (m:ℝ)^2 * x * (rFilter m).eval x ≤ 2 := by
  rcases eq_or_lt_of_le hx0 with h | hxpos
  · subst h; rw [rFilter_eval_zero m hm]; simp
  obtain ⟨u, hu0, hu1, hxu, hT⟩ := trig_rep m x hx0 hx1
  have hE := rFilter_eval_mul m hm x
  rw [hT] at hE
  set R := (rFilter m).eval x
  have hs : 0 < Real.sin u ^ 2 := by nlinarith
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hsin := abs_sin_nat_mul_le u m
  have hsq : Real.sin (m*u) ^ 2 ≤ (m:ℝ)^2 * Real.sin u ^ 2 := by
    rw [← sq_abs, ← sq_abs (Real.sin u)]
    nlinarith [abs_nonneg (Real.sin (m*u)), abs_nonneg (Real.sin u)]
  have key : (m:ℝ)^2 * Real.sin u ^ 2 * R = Real.sin (m*u) ^ 2 := by
    rw [hxu] at hE; nlinarith
  have hms : 0 < (m:ℝ)^2 * Real.sin u ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · by_contra hR; push Not at hR
    nlinarith [sq_nonneg (Real.sin (m*u)), mul_neg_of_pos_of_neg hms hR]
  · by_contra hR; push Not at hR
    nlinarith [mul_lt_mul_of_pos_left hR hms]
  · nlinarith [Real.sin_sq_le_one (m*u)]

set_option maxHeartbeats 1000000 in
lemma R_lower (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 2)
    (hsmall : (m:ℝ)^2 * x ≤ 1/8) :
    1 - (rFilter m).eval x ≤ (10/24) * ((m:ℝ)^2 * x) := by
  obtain ⟨u, hu0, hu1, hxu, hT⟩ := trig_rep m x hx0.le hx1
  have hE := rFilter_eval_mul m hm x
  rw [hT] at hE
  obtain ⟨R, hRdef⟩ : ∃ R, R = (rFilter m).eval x := ⟨_, rfl⟩
  rw [← hRdef] at hE ⊢
  have hs : 0 < Real.sin u ^ 2 := by nlinarith
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have key : (m:ℝ)^2 * Real.sin u ^ 2 * R = Real.sin (m*u) ^ 2 := by
    rw [hxu] at hE; nlinarith
  have hupos : 0 < u := by
    rcases eq_or_lt_of_le hu0 with h | h
    · subst h; simp at hs
    · exact h
  have hsinu_pos : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hupos (by linarith [Real.pi_pos])
  have hsinu_le : Real.sin u ≤ u := Real.sin_le hu0
  have hjordan : 2 / Real.pi * u ≤ Real.sin u := Real.mul_le_sin hu0 hu1
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 3 < Real.pi := Real.pi_gt_three
  -- u ≤ (π/2) sin u
  have hu_le : u ≤ Real.pi / 2 * Real.sin u := by
    have := mul_le_mul_of_nonneg_left hjordan (by positivity : (0:ℝ) ≤ Real.pi/2)
    field_simp at this ⊢; linarith
  have hu2 : u^2 ≤ (Real.pi/2)^2 * Real.sin u ^ 2 := by
    have := mul_self_le_mul_self hu0 hu_le
    nlinarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (m:ℝ) * u := ⟨_, rfl⟩
  rw [← hy] at key
  have hypos : 0 < y := by rw [hy]; positivity
  have hpi2 : Real.pi^2 ≤ 10 := by nlinarith
  have hy2 : y^2 ≤ (Real.pi^2/8) * ((m:ℝ)^2 * x) := by
    have e1 : y^2 = (m:ℝ)^2 * u^2 := by rw [hy]; ring
    have e2 := mul_le_mul_of_nonneg_left hu2 (sq_nonneg (m:ℝ))
    rw [e1]; rw [hxu]; nlinarith
  have hy2' : y^2 ≤ 1/4 := by
    have := mul_le_mul_of_nonneg_left hsmall (by positivity : (0:ℝ) ≤ Real.pi^2/8)
    nlinarith
  have hsiny := Real.sin_gt_sub_cube hypos
  have hpos' : 0 < y - y^3/6 := by
    have : y - y^3/6 = y * (1 - y^2/6) := by ring
    rw [this]; exact mul_pos hypos (by linarith)
  have hsq1 : y^2 * (1 - y^2/3) ≤ Real.sin y ^ 2 := by
    have h1 := mul_self_le_mul_self hpos'.le hsiny.le
    have h2 : y^2 * (1 - y^2/3) ≤ (y - y^3/6) * (y - y^3/6) := by
      have : (y - y^3/6) * (y - y^3/6) - y^2 * (1 - y^2/3) = y^6/36 := by ring
      nlinarith [pow_two_nonneg (y^3)]
    nlinarith
  have hsq2 : (m:ℝ)^2 * Real.sin u ^ 2 ≤ y^2 := by
    have h1 := mul_self_le_mul_self hsinu_pos.le hsinu_le
    have e1 : y^2 = (m:ℝ)^2 * u^2 := by rw [hy]; ring
    rw [e1]; exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
  have hms : 0 < (m:ℝ)^2 * Real.sin u ^ 2 := by positivity
  have hR : 1 - y^2/3 ≤ R := by
    by_contra hc; push Not at hc
    have h1 : (m:ℝ)^2 * Real.sin u ^ 2 * R < (m:ℝ)^2 * Real.sin u ^ 2 * (1 - y^2/3) :=
      mul_lt_mul_of_pos_left hc hms
    have h2 : (m:ℝ)^2 * Real.sin u ^ 2 * (1 - y^2/3) ≤ y^2 * (1 - y^2/3) :=
      mul_le_mul_of_nonneg_right hsq2 (by linarith)
    linarith
  have h3 := mul_le_mul_of_nonneg_right hpi2 (by positivity : (0:ℝ) ≤ (m:ℝ)^2 * x)

  clear hpi hpi0 hjordan hsiny key hE hT hxu
  calc 1 - R ≤ y^2/3 := by linarith
    _ ≤ (Real.pi^2/8) * ((m:ℝ)^2 * x) / 3 := by linarith
    _ = (Real.pi^2 * ((m:ℝ)^2 * x)) / 24 := by ring
    _ ≤ 10 * ((m:ℝ)^2 * x) / 24 := by linarith
    _ = (10/24) * ((m:ℝ)^2 * x) := by ring



lemma floor_facts (b : ℝ) (hb : 0 < b) (hb32 : b < 1/32) :
    1 ≤ ⌊1 / Real.sqrt (8*b)⌋₊ ∧
    8 * b * ((⌊1 / Real.sqrt (8*b)⌋₊ : ℕ) : ℝ)^2 ≤ 1 ∧
    1 ≤ 32 * b * ((⌊1 / Real.sqrt (8*b)⌋₊ : ℕ) : ℝ)^2 := by
  set s := Real.sqrt (8*b) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s^2 = 8*b := Real.sq_sqrt (by linarith)
  have hshalf : s < 1/2 := by nlinarith
  set m := ⌊1 / s⌋₊ with hm
  have hm1 : (m:ℝ) ≤ 1/s := Nat.floor_le (by positivity)
  have hm2 : 1/s < (m:ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : 2 < 1/s := by rw [lt_div_iff₀ hs0]; linarith
  have hmge : (1:ℝ) ≤ m := by linarith
  refine ⟨by exact_mod_cast hmge, ?_, ?_⟩
  · have : (m:ℝ) * s ≤ 1 := by rwa [le_div_iff₀ hs0] at hm1
    have h0 : 0 ≤ (m:ℝ) * s := by positivity
    have h1 : ((m:ℝ) * s)^2 ≤ 1 := by nlinarith
    rw [mul_pow, hs2] at h1; linarith
  · have h3 : 1/(2*s) ≤ (m:ℝ) := by
      have : 1/(2*s) = (1/s)/2 := by field_simp
      rw [this]; linarith
    have : 1 ≤ (m:ℝ) * (2*s) := by rwa [div_le_iff₀ (by positivity)] at h3
    nlinarith

end OTDLemma25

open OptimalTraceDistance.Estimation OTDLemma25 Polynomial

theorem solution (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
  ((filter b).natDegree : ℝ) ≤ b ^ (-(1/2 : ℝ)) ∧ (filter b).eval 0 = 1 ∧
  (∀ x ∈ Set.Icc (0 : ℝ) 1,
    0 ≤ (filter b).eval x ∧ (filter b).eval x ≤ 1 ∧
    x*((filter b).eval x)^2 ≤ (2 : ℝ)^7*b) ∧
  (∀ x ∈ Set.Icc (0 : ℝ) b,
    0 < (filter b).eval x ∧ -Real.log ((filter b).eval x) ≤ (x/b)^2) := by
  have hbinv : b ^ (-(1/2 : ℝ)) = Real.sqrt b⁻¹ := by
    rw [Real.rpow_neg hb.le, Real.sqrt_inv, Real.sqrt_eq_rpow]
  by_cases hbig : 1/32 ≤ b
  · have hf : filter b = 1 := by rw [filter, if_pos hbig]
    rw [hf, hbinv]
    refine ⟨by simpa using Real.sqrt_nonneg _, by simp, ?_, ?_⟩
    · intro x hx; simp only [eval_one]; refine ⟨by norm_num, le_rfl, ?_⟩
      nlinarith [hx.2]
    · intro x hx; simp only [eval_one, Real.log_one, neg_zero]
      exact ⟨by norm_num, sq_nonneg _⟩
  push Not at hbig
  obtain ⟨hm1, hmup, hmlo⟩ := floor_facts b hb hbig
  have hf : filter b = 2 * rFilter ⌊1 / Real.sqrt (8*b)⌋₊ - rFilter ⌊1 / Real.sqrt (8*b)⌋₊ ^ 2 := by
    rw [filter, if_neg (not_le.mpr hbig)]
  rw [hf]
  set m := ⌊1 / Real.sqrt (8*b)⌋₊ with hmdef
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
  have hevf : ∀ x, (2 * rFilter m - rFilter m ^ 2).eval x =
      2 * (rFilter m).eval x - ((rFilter m).eval x)^2 := by
    intro x; simp [eval_sub, eval_mul, eval_pow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- degree
    have hdeg : (2 * rFilter m - rFilter m ^ 2).natDegree ≤ 2 * m := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_mul_le).trans ?_
        have : (2 : ℝ[X]).natDegree = 0 := by
          rw [show (2:ℝ[X]) = C 2 from rfl]; exact natDegree_C _
        rw [this]; have := rFilter_natDegree m; omega
      · refine (natDegree_pow_le).trans ?_
        have := rFilter_natDegree m; omega
    rw [hbinv]
    calc ((2 * rFilter m - rFilter m ^ 2).natDegree : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast hdeg
      _ ≤ Real.sqrt b⁻¹ := by
        apply Real.le_sqrt_of_sq_le
        rw [le_inv_comm₀ ?_ hb] <;> push_cast
        · rw [show (2 * (m:ℝ))^2 = 4 * (m:ℝ)^2 by ring]
          rw [inv_eq_one_div, le_div_iff₀ (by positivity)]; nlinarith
        · positivity
  · rw [hevf, rFilter_eval_zero m hm1]; norm_num
  · intro x hx
    obtain ⟨hR0, hR1, hR2⟩ := R_bounds m hm1 x hx.1 (by linarith [hx.2])
    rw [hevf]
    set R := (rFilter m).eval x
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    have hf0 : 0 ≤ 2*R - R^2 := by nlinarith
    have hf1 : 2*R - R^2 ≤ 1 := by nlinarith
    have hf2 : 2*R - R^2 ≤ 2*R := by nlinarith
    have h4 : 4 / (m:ℝ)^2 ≤ 2^7 * b := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    by_cases hxs : x * (m:ℝ)^2 ≤ 4
    · have : x ≤ 4/(m:ℝ)^2 := by rw [le_div_iff₀ (by positivity)]; exact hxs
      have : x * (2*R - R^2)^2 ≤ x := by
        have := pow_le_one₀ hf0 hf1 (n := 2)
        nlinarith [hx.1]
      linarith
    · push Not at hxs
      -- x f² ≤ 4 x R² ≤ 16/(m⁴ x) ≤ 4/m²
      have hxpos : 0 < x := by
        by_contra h; push Not at h; nlinarith [sq_nonneg (m:ℝ)]
      have hA : x * (2*R - R^2)^2 ≤ 4 * x * R^2 := by
        have := mul_self_le_mul_self hf0 hf2
        nlinarith
      have hB : (m:ℝ)^2 * (4 * x * R^2) ≤ 4 := by
        -- (m² x R)² ≤ 4 and m² x ≥ 4
        have hsq : ((m:ℝ)^2 * x * R)^2 ≤ 4 := by
          have h0 : 0 ≤ (m:ℝ)^2 * x * R := by positivity
          nlinarith
        have : (m:ℝ)^2 * (4 * x * R^2) * ((m:ℝ)^2 * x) = 4 * ((m:ℝ)^2 * x * R)^2 := by ring
        have hmx : 4 ≤ (m:ℝ)^2 * x := by linarith
        nlinarith [sq_nonneg ((m:ℝ)^2 * x * R)]
      have : 4 * x * R^2 ≤ 4 / (m:ℝ)^2 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      linarith
  · intro x hx
    rw [hevf]
    rcases eq_or_lt_of_le hx.1 with h0 | hxpos
    · subst h0; rw [rFilter_eval_zero m hm1]; norm_num
    obtain ⟨hR0, hR1, -⟩ := R_bounds m hm1 x hx.1 (by linarith [hx.2])
    have hsmall : (m:ℝ)^2 * x ≤ 1/8 := by
      have : 8 * b * ((m:ℝ)^2 * x) ≤ b := by nlinarith [hx.2]
      nlinarith
    have hlow := R_lower m hm1 x hxpos (by linarith [hx.2]) hsmall
    set R := (rFilter m).eval x
    set t := x / b with ht
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hb]; exact hx.2
    have hmx : (m:ℝ)^2 * x ≤ t/8 := by
      rw [ht, le_div_iff₀ (by norm_num : (0:ℝ) < 8)]
      rw [le_div_iff₀ hb]; nlinarith
    have h1R : 1 - R ≤ t/19 := by nlinarith
    have hsq : (1 - R)^2 ≤ t^2/361 := by
      have h0 : 0 ≤ 1 - R := by linarith
      have := mul_self_le_mul_self h0 h1R
      nlinarith
    have hfe : 2*R - R^2 = 1 - (1-R)^2 := by ring
    rw [hfe]
    have hfpos : 360/361 ≤ 1 - (1-R)^2 := by nlinarith
    refine ⟨by linarith, ?_⟩
    have hlog := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 - (1-R)^2)
    have hinv : (1 - (1-R)^2)⁻¹ - 1 ≤ t^2 := by
      rw [inv_eq_one_div, div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg t]
    linarith


