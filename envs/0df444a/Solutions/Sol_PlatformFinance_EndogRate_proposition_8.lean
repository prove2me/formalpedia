-- Prove2me | solution 1 for PlatformFinance.EndogRate.proposition_8
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-22T18:19:26.912371+00:00
-- url     : https://prove2.me/submissions/454dae52-0d0a-4265-b092-4599a514a389

import Definitions.Def_PlatformFinance_EndogRate_Model

namespace PlatformFinance.EndogRate

open MeasureTheory

noncomputable section

/-! ### Integrals of piecewise-linear integrands -/

lemma int_lin {f : ℝ → ℝ} {l u α β : ℝ} (hab : l ≤ u)
    (h : ∀ x ∈ Set.Icc l u, f x = α + β * x) :
    ∫ x in l..u, f x = α * (u - l) + β * (u ^ 2 - l ^ 2) / 2 := by
  rw [intervalIntegral.integral_congr (g := fun x => α + β * x)]
  · rw [intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun x : ℝ => β * x).intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
    simp; ring
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact h x hx

lemma integrand_cont (φ W q : ℝ) :
    Continuous (fun x : ℝ => max ((1 - φ) * (x - q) * q - W * q) 0) := by fun_prop

/-! ### The seller's expected payoff in closed form -/

lemma seller_r1 {a δ φ W q : ℝ} (hk : 0 < 1 - φ) (hδ : 0 < δ) (hq : 0 ≤ q)
    (h : (1 - φ) * q + W ≤ (1 - φ) * (a - δ)) :
    sellerPayoff a δ φ W q = q * ((1 - φ) * (a - q) - W) := by
  unfold sellerPayoff uniformMean
  rw [int_lin (α := -(1 - φ) * q * q - W * q) (β := (1 - φ) * q) (by linarith)]
  · field_simp; ring
  · intro x hx
    have hx1 : (1 - φ) * (a - δ) ≤ (1 - φ) * x := mul_le_mul_of_nonneg_left hx.1 hk.le
    have e : (1 - φ) * (x - q) * q - W * q = q * ((1 - φ) * x - (1 - φ) * q - W) := by ring
    rw [e, max_eq_left (mul_nonneg hq (by linarith))]; ring

lemma seller_r2 {a δ φ W q : ℝ} (hk : 0 < 1 - φ) (hδ : 0 < δ) (hq : 0 ≤ q)
    (h1 : (1 - φ) * (a - δ) ≤ (1 - φ) * q + W) (h2 : (1 - φ) * q + W ≤ (1 - φ) * (a + δ)) :
    sellerPayoff a δ φ W q =
      q * ((1 - φ) * (a + δ) - (1 - φ) * q - W) ^ 2 / (4 * δ * (1 - φ)) := by
  unfold sellerPayoff uniformMean
  have hk0 : (1 - φ) ≠ 0 := hk.ne'
  obtain ⟨T, hT⟩ : ∃ T, T = q + W / (1 - φ) := ⟨_, rfl⟩
  have hkT : (1 - φ) * T = (1 - φ) * q + W := by rw [hT]; field_simp
  have hT1 : a - δ ≤ T := by
    by_contra hc; push Not at hc
    have := mul_lt_mul_of_pos_left hc hk; linarith
  have hT2 : T ≤ a + δ := by
    by_contra hc; push Not at hc
    have := mul_lt_mul_of_pos_left hc hk; linarith
  have hi := fun l u => (integrand_cont φ W q).intervalIntegrable (μ := volume) l u
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (a - δ) T) (hi T (a + δ))]
  rw [int_lin (α := 0) (β := 0) hT1,
    int_lin (α := -(1 - φ) * q * q - W * q) (β := (1 - φ) * q) hT2]
  · have hW : W = (1 - φ) * T - (1 - φ) * q := by linarith
    subst hW
    field_simp; ring
  · intro x hx
    have hx1 : (1 - φ) * T ≤ (1 - φ) * x := mul_le_mul_of_nonneg_left hx.1 hk.le
    have e : (1 - φ) * (x - q) * q - W * q = q * ((1 - φ) * x - (1 - φ) * q - W) := by ring
    rw [e, max_eq_left (mul_nonneg hq (by linarith))]; ring
  · intro x hx
    have hx1 : (1 - φ) * x ≤ (1 - φ) * T := mul_le_mul_of_nonneg_left hx.2 hk.le
    have e : (1 - φ) * (x - q) * q - W * q = q * ((1 - φ) * x - (1 - φ) * q - W) := by ring
    rw [e, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hq (by linarith))]; ring

lemma seller_r3 {a δ φ W q : ℝ} (hk : 0 < 1 - φ) (hδ : 0 < δ) (hq : 0 ≤ q)
    (h : (1 - φ) * (a + δ) ≤ (1 - φ) * q + W) : sellerPayoff a δ φ W q = 0 := by
  unfold sellerPayoff uniformMean
  rw [int_lin (α := 0) (β := 0) (by linarith)]
  · ring
  · intro x hx
    have hx1 : (1 - φ) * x ≤ (1 - φ) * (a + δ) := mul_le_mul_of_nonneg_left hx.2 hk.le
    have e : (1 - φ) * (x - q) * q - W * q = q * ((1 - φ) * x - (1 - φ) * q - W) := by ring
    rw [e, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hq (by linarith))]; ring

/-! ### Polynomial inequalities -/

lemma poly1 {A D U : ℝ} (hD : 0 < D) (hA : 2 * D ≤ A) (hU0 : 0 ≤ U) (hU : U < 2 * D) :
    (A + D - U) * U ^ 2 < D * A ^ 2 := by
  have h1 : 0 < 2 * D - U := by linarith
  have h2 : 0 ≤ A - 2 * D := by linarith
  nlinarith [mul_nonneg hD.le (sq_nonneg (A - 2 * D)),
    mul_pos (mul_pos h1 h1) (show 0 < U + D by linarith),
    mul_nonneg (mul_nonneg h1.le h2) (show 0 ≤ U + 2 * D by linarith)]

lemma poly2 {B U : ℝ} (hB : 0 < B) (hU0 : 0 ≤ U) (hne : 3 * U - 2 * B ≠ 0) :
    27 * ((B - U) * U ^ 2) < 4 * B ^ 3 := by
  nlinarith [mul_pos (pow_pos (abs_pos.mpr hne) 2) (show 0 < 3 * U + B by linarith),
    sq_abs (3 * U - 2 * B)]

lemma poly3 {B D x : ℝ} (hD : 0 < D) (hB0 : 0 < B) (hB : B < 3 * D) (hx0 : 0 ≤ x)
    (hx : x ≤ B - 2 * D) : 27 * D * (x * (B - D - x)) < B ^ 3 := by
  have h1 : 0 ≤ (B - 2 * D - x) * (D - x) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 < (B - 3 * D) ^ 2 * (B + 6 * D) :=
    mul_pos (pow_pos (abs_pos.mpr (show B - 3 * D ≠ 0 by linarith)) 2 |>.trans_eq
      (sq_abs _)) (by linarith)
  nlinarith [mul_nonneg hD.le h1]

/-! ### The seller's best response is unique -/

lemma strict1 {a δ φ W : ℝ} (hk : 0 < 1 - φ) (hδ : 0 < δ) (hW : W ≤ (1 - φ) * (a - 2 * δ))
    (q : ℝ) (hq : 0 ≤ q) (hne : q ≠ ((1 - φ) * a - W) / (2 * (1 - φ))) :
    sellerPayoff a δ φ W q < sellerPayoff a δ φ W (((1 - φ) * a - W) / (2 * (1 - φ))) := by
  obtain ⟨A, rfl⟩ : ∃ A, W = (1 - φ) * a - A := ⟨(1 - φ) * a - W, by ring⟩
  have hk0 := hk.ne'
  have hD : 0 < (1 - φ) * δ := mul_pos hk hδ
  have hA : 2 * ((1 - φ) * δ) ≤ A := by linarith
  have e2 : (1 - φ) * a - ((1 - φ) * a - A) = A := by ring
  rw [e2] at hne ⊢
  have hq1pos : 0 ≤ A / (2 * (1 - φ)) := div_nonneg (by linarith) (by linarith)
  have hq1 : (1 - φ) * (A / (2 * (1 - φ))) = A / 2 := by field_simp
  rw [seller_r1 hk hδ hq1pos (by rw [hq1]; linarith)]
  have hv : A / (2 * (1 - φ)) * ((1 - φ) * (a - A / (2 * (1 - φ))) - ((1 - φ) * a - A))
      = A ^ 2 / (4 * (1 - φ)) := by field_simp; ring
  rw [hv]
  have hne' : 2 * ((1 - φ) * q) - A ≠ 0 := by
    intro h; apply hne; field_simp; linarith
  have h4k : 0 < 4 * (1 - φ) := by linarith
  rcases le_or_gt ((1 - φ) * q + ((1 - φ) * a - A)) ((1 - φ) * (a - δ)) with h1 | h1
  · rw [seller_r1 hk hδ hq h1, lt_div_iff₀ h4k]
    nlinarith [pow_pos (abs_pos.mpr hne') 2, sq_abs (2 * ((1 - φ) * q) - A)]
  rcases le_or_gt ((1 - φ) * q + ((1 - φ) * a - A)) ((1 - φ) * (a + δ)) with h2 | h2
  · rw [seller_r2 hk hδ hq h1.le h2, div_lt_div_iff₀ (by nlinarith) h4k]
    have := poly1 (A := A) (D := (1 - φ) * δ)
      (U := (1 - φ) * (a + δ) - (1 - φ) * q - ((1 - φ) * a - A)) hD hA (by linarith)
      (by linarith)
    nlinarith [this]
  · rw [seller_r3 hk hδ hq h2.le]
    exact div_pos (pow_pos (by linarith) 2) h4k

lemma strict2 {a δ φ W : ℝ} (hk : 0 < 1 - φ) (hδ : 0 < δ) (hW1 : (1 - φ) * (a - 2 * δ) < W)
    (hW2 : W < (1 - φ) * (a + δ)) (q : ℝ) (hq : 0 ≤ q)
    (hne : q ≠ ((1 - φ) * (a + δ) - W) / (3 * (1 - φ))) :
    sellerPayoff a δ φ W q < sellerPayoff a δ φ W (((1 - φ) * (a + δ) - W) / (3 * (1 - φ))) := by
  obtain ⟨B, rfl⟩ : ∃ B, W = (1 - φ) * (a + δ) - B := ⟨(1 - φ) * (a + δ) - W, by ring⟩
  have hk0 := hk.ne'
  have hD : 0 < (1 - φ) * δ := mul_pos hk hδ
  have hB0 : 0 < B := by linarith
  have hB3 : B < 3 * ((1 - φ) * δ) := by linarith
  have e2 : (1 - φ) * (a + δ) - ((1 - φ) * (a + δ) - B) = B := by ring
  rw [e2] at hne ⊢
  have hq2pos : 0 ≤ B / (3 * (1 - φ)) := div_nonneg hB0.le (by linarith)
  have hq2 : (1 - φ) * (B / (3 * (1 - φ))) = B / 3 := by field_simp
  rw [seller_r2 hk hδ hq2pos (by rw [hq2]; linarith) (by rw [hq2]; linarith)]
  have hv : B / (3 * (1 - φ)) * ((1 - φ) * (a + δ) - (1 - φ) * (B / (3 * (1 - φ)))
      - ((1 - φ) * (a + δ) - B)) ^ 2 / (4 * δ * (1 - φ)) = B ^ 3 / (27 * δ * (1 - φ) ^ 2) := by
    field_simp; ring
  rw [hv]
  have hne' : 3 * (B - (1 - φ) * q) - 2 * B ≠ 0 := by
    intro h; apply hne; field_simp; linarith
  have hden : 0 < 27 * δ * (1 - φ) ^ 2 := mul_pos (mul_pos (by norm_num) hδ) (pow_pos hk 2)
  have hxq : 0 ≤ (1 - φ) * q := mul_nonneg hk.le hq
  rcases le_or_gt ((1 - φ) * q + ((1 - φ) * (a + δ) - B)) ((1 - φ) * (a - δ)) with h1 | h1
  · rw [seller_r1 hk hδ hq h1, lt_div_iff₀ hden]
    have := poly3 (B := B) (D := (1 - φ) * δ) (x := (1 - φ) * q) hD hB0 hB3 hxq (by linarith)
    nlinarith [this]
  rcases le_or_gt ((1 - φ) * q + ((1 - φ) * (a + δ) - B)) ((1 - φ) * (a + δ)) with h2 | h2
  · rw [seller_r2 hk hδ hq h1.le h2, div_lt_div_iff₀ (by nlinarith) hden]
    have h := mul_lt_mul_of_pos_left
      (poly2 (B := B) (U := B - (1 - φ) * q) hB0 (by linarith) hne') (mul_pos hδ hk)
    nlinarith [h]
  · rw [seller_r3 hk hδ hq h2.le]
    exact div_pos (pow_pos hB0 3) hden

lemma order_of_strict {S : ℝ → ℝ} {qs qo : ℝ} (hqo : 0 ≤ qo) (hopt : S qs ≤ S qo)
    (hstrict : ∀ q, 0 ≤ q → q ≠ qs → S q < S qs) : qo = qs := by
  by_contra h
  exact absurd hopt (not_le.mpr (hstrict qo hqo h))

lemma order1 {a δ φ : ℝ} {owed order : ℝ → ℝ} (hk : 0 < 1 - φ) (hδ : 0 < δ)
    (hs : IsSellerRule a δ φ owed order) (w : ℝ) (hW : owed w ≤ (1 - φ) * (a - 2 * δ)) :
    order w = ((1 - φ) * a - owed w) / (2 * (1 - φ)) :=
  order_of_strict (hs w).1
    ((hs w).2.1 _ (div_nonneg (by nlinarith [mul_pos hk hδ]) (by linarith)))
    (strict1 hk hδ hW)

lemma order2 {a δ φ : ℝ} {owed order : ℝ → ℝ} (hk : 0 < 1 - φ) (hδ : 0 < δ)
    (hs : IsSellerRule a δ φ owed order) (w : ℝ) (hW1 : (1 - φ) * (a - 2 * δ) < owed w)
    (hW2 : owed w < (1 - φ) * (a + δ)) :
    order w = ((1 - φ) * (a + δ) - owed w) / (3 * (1 - φ)) :=
  order_of_strict (hs w).1
    ((hs w).2.1 _ (div_nonneg (by linarith) (by linarith)))
    (strict2 hk hδ hW1 hW2)

lemma order3 {a δ φ : ℝ} {owed order : ℝ → ℝ} (hk : 0 < 1 - φ) (hδ : 0 < δ)
    (hs : IsSellerRule a δ φ owed order) (w : ℝ) (hW : (1 - φ) * (a + δ) ≤ owed w) :
    order w = 0 :=
  (hs w).2.2 (fun q hq => (seller_r3 hk hδ hq (by nlinarith [mul_nonneg hk.le hq])).le)

/-! ### The supplier's problem -/

def w1f (a φ c r : ℝ) : ℝ := ((1 - φ) * a + c * (1 + r)) / (2 * (1 + r))

def q1f (a φ c r : ℝ) : ℝ := ((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ))

lemma sqrt6_ge : (2 : ℝ) ≤ √6 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]

lemma w1f_mul {a φ c r : ℝ} (hr : -1 < r) :
    w1f a φ c r * (1 + r) = ((1 - φ) * a + c * (1 + r)) / 2 := by
  have : (1 : ℝ) + r ≠ 0 := by linarith
  unfold w1f; field_simp

lemma order_w1 {a δ φ c r : ℝ} {order : ℝ → ℝ} (hk : 0 < 1 - φ) (hδ : 0 < δ) (hr : -1 < r)
    (hs : IsSellerRule a δ φ (fun w => w * (1 + r)) order)
    (hreg : (2 + √6) * ((1 - φ) * δ) ≤ (1 - φ) * a - c * (1 + r)) :
    order (w1f a φ c r) = q1f a φ c r := by
  have hD := mul_pos hk hδ
  have h6 := mul_le_mul_of_nonneg_right sqrt6_ge hD.le
  have := order1 hk hδ hs (w1f a φ c r) (by beta_reduce; rw [w1f_mul hr]; nlinarith)
  rw [this]; beta_reduce; rw [w1f_mul hr]; unfold q1f
  have hk0 := hk.ne'
  field_simp; ring

lemma supplier_bound {a δ φ c rf r : ℝ} {order : ℝ → ℝ} (hk : 0 < 1 - φ) (hδ : 0 < δ)
    (hc : 0 < c) (hR : 0 < 1 + rf) (hr : -1 < r)
    (hs : IsSellerRule a δ φ (fun w => w * (1 + r)) order)
    (hreg : (2 + √6) * ((1 - φ) * δ) ≤ (1 - φ) * a - c * (1 + r)) (w' : ℝ) :
    supplierPayoffP c rf w' (order w') ≤
        supplierPayoffP c rf (w1f a φ c r) (order (w1f a φ c r)) ∧
      (w' < w1f a φ c r → supplierPayoffP c rf w' (order w') <
        supplierPayoffP c rf (w1f a φ c r) (order (w1f a φ c r))) := by
  have hs1 : 0 < 1 + r := by linarith
  have hs0 : (1 : ℝ) + r ≠ 0 := hs1.ne'
  have hk0 := hk.ne'
  have hD := mul_pos hk hδ
  have h6 := mul_le_mul_of_nonneg_right sqrt6_ge hD.le
  have hE : 0 < (1 - φ) * a - c * (1 + r) := by nlinarith
  rw [order_w1 hk hδ hr hs hreg]
  have hden : 0 < 8 * (1 - φ) * (1 + r) := mul_pos (mul_pos (by norm_num) hk) hs1
  have hV : supplierPayoffP c rf (w1f a φ c r) (q1f a φ c r) =
      ((1 - φ) * a - c * (1 + r)) ^ 2 / (8 * (1 - φ) * (1 + r)) * (1 + rf) := by
    unfold supplierPayoffP w1f q1f; field_simp; ring
  rw [hV]
  have hVpos : 0 < ((1 - φ) * a - c * (1 + r)) ^ 2 / (8 * (1 - φ) * (1 + r)) * (1 + rf) :=
    mul_pos (div_pos (pow_pos hE 2) hden) hR
  have hq0 := (hs w').1
  have hW1 := w1f_mul (a := a) (φ := φ) (c := c) hr
  unfold supplierPayoffP
  obtain ⟨W, hWdef⟩ : ∃ W, W = w' * (1 + r) := ⟨_, rfl⟩
  have hw' : w' = W / (1 + r) := by rw [hWdef]; field_simp
  by_cases hwc : w' ≤ c
  · have : (w' - c) * order w' * (1 + rf) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) hq0) hR.le
    exact ⟨by linarith, fun _ => by linarith⟩
  push Not at hwc
  have hWC : c * (1 + r) < W := by rw [hWdef]; exact mul_lt_mul_of_pos_right hwc hs1
  rcases le_or_gt W ((1 - φ) * (a - 2 * δ)) with h1 | h1
  · have ho := order1 hk hδ hs w' (by beta_reduce; rw [← hWdef]; exact h1)
    beta_reduce at ho; rw [← hWdef] at ho
    rw [ho]
    have key : (w' - c) * (((1 - φ) * a - W) / (2 * (1 - φ))) =
        (((1 - φ) * a - c * (1 + r)) ^ 2 - (2 * W - (1 - φ) * a - c * (1 + r)) ^ 2) /
          (8 * (1 - φ) * (1 + r)) := by rw [hw']; field_simp; ring
    rw [key]
    constructor
    · apply mul_le_mul_of_nonneg_right _ hR.le
      rw [div_le_div_iff₀ hden hden]
      nlinarith [mul_nonneg (sq_nonneg (2 * W - (1 - φ) * a - c * (1 + r))) hden.le]
    · intro hlt
      apply mul_lt_mul_of_pos_right _ hR
      rw [div_lt_div_iff₀ hden hden]
      have hlt2 : W < ((1 - φ) * a + c * (1 + r)) / 2 := by
        rw [hWdef, ← hW1]; exact mul_lt_mul_of_pos_right hlt hs1
      have hsq : 0 < (2 * W - (1 - φ) * a - c * (1 + r)) ^ 2 := by
        have : 2 * W - (1 - φ) * a - c * (1 + r) < 0 := by linarith
        nlinarith [this]
      nlinarith [mul_pos hsq hden]
  rcases lt_or_ge W ((1 - φ) * (a + δ)) with h2 | h2
  · have ho := order2 hk hδ hs w' (by beta_reduce; rw [← hWdef]; exact h1)
      (by beta_reduce; rw [← hWdef]; exact h2)
    beta_reduce at ho; rw [← hWdef] at ho
    rw [ho]
    have key : (w' - c) * (((1 - φ) * (a + δ) - W) / (3 * (1 - φ))) =
        (W - c * (1 + r)) * ((1 - φ) * (a + δ) - W) / (3 * (1 - φ) * (1 + r)) := by
      rw [hw']; field_simp
    rw [key]
    have hden3 : 0 < 3 * (1 - φ) * (1 + r) := mul_pos (mul_pos (by norm_num) hk) hs1
    have hsq6 : 2 * ((1 - φ) * a - c * (1 + r) + (1 - φ) * δ) ^ 2 ≤
        3 * ((1 - φ) * a - c * (1 + r)) ^ 2 := by
      have hm := mul_nonneg (sub_nonneg.2 hreg)
        (show 0 ≤ (1 - φ) * a - c * (1 + r) + (√6 - 2) * ((1 - φ) * δ) by nlinarith)
      have h66 : √6 * √6 * ((1 - φ) * δ) ^ 2 = 6 * ((1 - φ) * δ) ^ 2 := by
        rw [Real.mul_self_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]
      linarith [hm, h66]
    have hamgm : 4 * ((W - c * (1 + r)) * ((1 - φ) * (a + δ) - W)) ≤
        ((1 - φ) * (a + δ) - c * (1 + r)) ^ 2 := by
      linarith [sq_nonneg (2 * W - (1 - φ) * (a + δ) - c * (1 + r))]
    have hle : (W - c * (1 + r)) * ((1 - φ) * (a + δ) - W) / (3 * (1 - φ) * (1 + r)) ≤
        ((1 - φ) * a - c * (1 + r)) ^ 2 / (8 * (1 - φ) * (1 + r)) := by
      rw [div_le_div_iff₀ hden3 hden]
      have e : (1 - φ) * (a + δ) - c * (1 + r) = (1 - φ) * a - c * (1 + r) + (1 - φ) * δ := by
        ring
      rw [e] at hamgm
      have hprod : 0 < (1 - φ) * (1 + r) := mul_pos hk hs1
      linarith [mul_le_mul_of_nonneg_left hamgm hprod.le,
        mul_le_mul_of_nonneg_left hsq6 hprod.le]
    refine ⟨mul_le_mul_of_nonneg_right hle hR.le, fun hlt => ?_⟩
    exfalso
    have hlt2 : W < ((1 - φ) * a + c * (1 + r)) / 2 := by
      rw [hWdef, ← hW1]; exact mul_lt_mul_of_pos_right hlt hs1
    linarith
  · have ho := order3 hk hδ hs w' (by beta_reduce; rw [← hWdef]; exact h2)
    rw [ho]
    simp only [mul_zero, zero_mul]
    exact ⟨hVpos.le, fun _ => hVpos⟩

lemma spe_w {a δ φ c rf r : ℝ} {σ : Profile} (hk : 0 < 1 - φ) (hδ : 0 < δ)
    (hc : 0 < c) (hR : 0 < 1 + rf) (hr : -1 < r)
    (hreg : (2 + √6) * ((1 - φ) * δ) ≤ (1 - φ) * a - c * (1 + r))
    (h : IsSPEP a δ φ c rf r σ) : σ.w = w1f a φ c r := by
  obtain ⟨hs, hopt, hleast⟩ := h
  have hb := supplier_bound hk hδ hc hR hr hs hreg
  rcases lt_trichotomy σ.w (w1f a φ c r) with hlt | heq | hgt
  · exact absurd (hopt (w1f a φ c r)) (not_le.mpr ((hb σ.w).2 hlt))
  · exact heq
  · exact absurd (hb σ.w).1 (not_le.mpr (hleast _ hgt))

/-! ### The platform's equilibrium profit -/

lemma platform_eq {a δ φ rf r w q : ℝ} (hk : 0 < 1 - φ) (hδ : 0 < δ) (hq : 0 ≤ q)
    (h : (1 - φ) * q + w * (1 + r) ≤ (1 - φ) * (a - δ)) :
    platformPayoffP a δ φ rf r w q = φ * (a - q) * q + w * q * (1 + r) - w * q * (1 + rf) := by
  unfold platformPayoffP uniformMean
  rw [int_lin (α := -φ * q * q + w * q * (1 + r)) (β := φ * q) (by linarith)]
  · field_simp; ring
  · intro x hx
    have hx1 : (1 - φ) * (a - δ) ≤ (1 - φ) * x := mul_le_mul_of_nonneg_left hx.1 hk.le
    have hm := mul_nonneg hq (show 0 ≤ (1 - φ) * x - (1 - φ) * q - w * (1 + r) by linarith)
    rw [min_eq_right (by nlinarith [hm])]
    ring

def Pi (a φ c rf r : ℝ) : ℝ :=
  φ * (a - q1f a φ c r) * q1f a φ c r + w1f a φ c r * q1f a φ c r * (1 + r)
    - w1f a φ c r * q1f a φ c r * (1 + rf)

lemma profit_eq {a δ φ c rf r : ℝ} {σ : Profile} (hk : 0 < 1 - φ) (hδ : 0 < δ)
    (hc : 0 < c) (hR : 0 < 1 + rf) (hr : -1 < r)
    (hreg : (2 + √6) * ((1 - φ) * δ) ≤ (1 - φ) * a - c * (1 + r))
    (h : IsSPEP a δ φ c rf r σ) : platformProfitP a δ φ rf r σ = Pi a φ c rf r := by
  have hw := spe_w hk hδ hc hR hr hreg h
  have ho := order_w1 hk hδ hr h.1 hreg
  unfold platformProfitP Pi
  rw [hw, ho]
  have hD := mul_pos hk hδ
  have h6 := mul_le_mul_of_nonneg_right sqrt6_ge hD.le
  have hk0 := hk.ne'
  have hq : (1 - φ) * q1f a φ c r = ((1 - φ) * a - c * (1 + r)) / 4 := by
    unfold q1f; field_simp
  apply platform_eq hk hδ
  · unfold q1f; exact div_nonneg (by nlinarith) (by linarith)
  · rw [hq, w1f_mul hr]; nlinarith

/-! ### Optimisation over the loan rate -/

def Nf (a φ c rf r : ℝ) : ℝ :=
  2 * a ^ 2 * (1 - φ) ^ 3
    - (1 + r) * (2 * a * c * (1 - φ) * φ + (1 + rf) * c ^ 2 * φ + c ^ 2 * (2 - φ) * (1 + r))

lemma Pi_diff {a φ c rf r : ℝ} (hk : 0 < 1 - φ) (hR : 0 < 1 + rf) (hr : -1 < r) :
    Pi a φ c rf rf - Pi a φ c rf r = (rf - r) * Nf a φ c rf r / (16 * (1 - φ) ^ 2 * (1 + r)) := by
  have h1 : (1 : ℝ) + r ≠ 0 := by linarith
  have h2 : (1 : ℝ) + rf ≠ 0 := hR.ne'
  have hk0 := hk.ne'
  unfold Pi w1f q1f Nf
  field_simp
  ring

lemma N_expand (a φ c rf r : ℝ) :
    Nf a φ c rf r - Nf a φ c rf rf = (rf - r) * (2 * a * c * (1 - φ) * φ + (1 + rf) * c ^ 2 * φ
      + c ^ 2 * (2 - φ) * ((1 + rf) + (1 + r))) := by
  unfold Nf; ring

lemma N_rf (a φ c rf : ℝ) :
    Nf a φ c rf rf = 2 * a ^ 2 * (1 - φ) ^ 3 - 2 * a * (1 - φ) * φ * (c * (1 + rf))
      - 2 * (c * (1 + rf)) ^ 2 := by
  unfold Nf; ring

lemma Pi_cont {a φ c rf r0 : ℝ} (hr0 : -1 < r0) :
    ContinuousOn (Pi a φ c rf) (Set.Icc r0 rf) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have h2 : (2 : ℝ) * (1 + x) ≠ 0 := (by linarith [hx.1] : (0 : ℝ) < 2 * (1 + x)).ne'
  unfold Pi w1f q1f
  fun_prop (disch := assumption)

/-- Proposition 8. -/
theorem proposition_8 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (hδ2 : δ ≤ delta2 a φ c rf)
    (σP : ℝ → Profile)
    (hP : ∀ r : ℝ, -1 < r → r ≤ rhat1 a δ φ c rf → IsSPEP a δ φ c rf r (σP r)) :
    (c ≤ cbar a φ rf →
      -1 < rf ∧ rf ≤ rhat1 a δ φ c rf ∧
        ∀ r : ℝ, -1 < r → r ≤ rhat1 a δ φ c rf → r ≠ rf →
          platformProfitP a δ φ rf r (σP r) < platformProfitP a δ φ rf rf (σP rf)) ∧
    (cbar a φ rf < c →
      (∃ rs : ℝ, -1 < rs ∧ rs ≤ rhat1 a δ φ c rf ∧
        ∀ r : ℝ, -1 < r → r ≤ rhat1 a δ φ c rf →
          platformProfitP a δ φ rf r (σP r) ≤ platformProfitP a δ φ rf rs (σP rs)) ∧
      ∀ rs : ℝ, -1 < rs → rs ≤ rhat1 a δ φ c rf →
        (∀ r : ℝ, -1 < r → r ≤ rhat1 a δ φ c rf →
          platformProfitP a δ φ rf r (σP r) ≤ platformProfitP a δ φ rf rs (σP rs)) →
        rs < rf) := by
  have hk : 0 < 1 - φ := by linarith
  have hR : 0 < 1 + rf := by linarith
  have ha : 0 < a := by linarith
  have hrh : rhat1 a δ φ c rf = rf := by unfold rhat1; rw [if_pos hδ2]
  have hreg0 : (2 + √6) * ((1 - φ) * δ) ≤ (1 - φ) * a - c * (1 + rf) := by
    have h := hδ2
    unfold delta2 at h
    rw [le_div_iff₀ (mul_pos (by positivity) hk)] at h
    linarith
  have hregr : ∀ r, r ≤ rf → (2 + √6) * ((1 - φ) * δ) ≤ (1 - φ) * a - c * (1 + r) := by
    intro r hr; nlinarith
  have hPi : ∀ r, -1 < r → r ≤ rf → platformProfitP a δ φ rf r (σP r) = Pi a φ c rf r := by
    intro r hr1 hr2
    exact profit_eq hk hδ hc hR hr1 (hregr r hr2) (hP r hr1 (by rw [hrh]; exact hr2))
  have hden : ∀ r : ℝ, -1 < r → 0 < 16 * (1 - φ) ^ 2 * (1 + r) := fun r hr =>
    mul_pos (mul_pos (by norm_num) (pow_pos hk 2)) (by linarith)
  -- nonnegative coefficients
  have hX : 0 ≤ 2 * a * c * (1 - φ) * φ + (1 + rf) * c ^ 2 * φ := by
    have h1 : 0 ≤ 2 * a * c * (1 - φ) * φ :=
      mul_nonneg (mul_nonneg (by positivity) hk.le) hφ0
    have h2 : 0 ≤ (1 + rf) * c ^ 2 * φ := mul_nonneg (mul_nonneg hR.le (sq_nonneg c)) hφ0
    linarith
  have hc2 : 0 < c ^ 2 * (2 - φ) := mul_pos (pow_pos hc 2) (by linarith)
  have hakφ : 0 ≤ 2 * a * (1 - φ) * φ := mul_nonneg (mul_nonneg (by positivity) hk.le) hφ0
  have hY : 0 < a * (1 - φ) ^ 2 := mul_pos ha (pow_pos hk 2)
  have hy : 0 < c * (1 + rf) := mul_pos hc hR
  rw [hrh]
  refine ⟨?_, ?_⟩
  · intro hcb
    have hcR : c * (1 + rf) ≤ a * (1 - φ) ^ 2 := by
      unfold cbar at hcb; rwa [le_div_iff₀ hR] at hcb
    refine ⟨by linarith, le_rfl, ?_⟩
    intro r hr1 hr2 hne
    have hlt : r < rf := lt_of_le_of_ne hr2 hne
    rw [hPi r hr1 hr2, hPi rf (by linarith) le_rfl]
    have hNrf : 0 ≤ Nf a φ c rf rf := by
      rw [N_rf]
      have e1 := mul_le_mul_of_nonneg_left hcR hakφ
      have e2 := mul_le_mul hcR hcR hy.le hY.le
      have e3 : 2 * a ^ 2 * (1 - φ) ^ 3 - 2 * a * (1 - φ) * φ * (a * (1 - φ) ^ 2)
          - 2 * (a * (1 - φ) ^ 2) ^ 2 = 0 := by ring
      nlinarith
    have hN : 0 < Nf a φ c rf r := by
      have e := N_expand a φ c rf r
      have hpos : 0 < (rf - r) * (2 * a * c * (1 - φ) * φ + (1 + rf) * c ^ 2 * φ
          + c ^ 2 * (2 - φ) * ((1 + rf) + (1 + r))) :=
        mul_pos (by linarith) (by nlinarith)
      linarith
    have := Pi_diff (a := a) (c := c) hk hR hr1
    have : 0 < (rf - r) * Nf a φ c rf r / (16 * (1 - φ) ^ 2 * (1 + r)) :=
      div_pos (mul_pos (by linarith) hN) (hden r hr1)
    linarith
  · intro hcb
    have hcR : a * (1 - φ) ^ 2 < c * (1 + rf) := by
      unfold cbar at hcb; rwa [div_lt_iff₀ hR] at hcb
    have hNrf : Nf a φ c rf rf < 0 := by
      rw [N_rf]
      have e1 := mul_le_mul_of_nonneg_left hcR.le hakφ
      have e2 := mul_lt_mul'' hcR hcR hY.le hY.le
      have e3 : 2 * a ^ 2 * (1 - φ) ^ 3 - 2 * a * (1 - φ) * φ * (a * (1 - φ) ^ 2)
          - 2 * (a * (1 - φ) ^ 2) ^ 2 = 0 := by ring
      nlinarith
    refine ⟨?_, ?_⟩
    · -- existence of an optimal rate
      obtain ⟨K', hK'⟩ : ∃ K', K' = 2 * a * c * (1 - φ) * φ + (1 + rf) * c ^ 2 * φ + c ^ 2 * (2 - φ) * (1 + rf) :=
        ⟨_, rfl⟩
      have hK'pos : 0 < K' := by
        have : 0 < c ^ 2 * (2 - φ) * (1 + rf) := mul_pos hc2 hR
        linarith
      have hM : 0 < a ^ 2 * (1 - φ) ^ 3 := mul_pos (pow_pos ha 2) (pow_pos hk 3)
      set s0 := min (1 + rf) (a ^ 2 * (1 - φ) ^ 3 / K') with hs0
      have hs0pos : 0 < s0 := lt_min hR (div_pos hM hK'pos)
      have hs0R : s0 ≤ 1 + rf := min_le_left _ _
      have hs0M : s0 ≤ a ^ 2 * (1 - φ) ^ 3 / K' := min_le_right _ _
      have hr0 : -1 < s0 - 1 := by linarith
      have hr0rf : s0 - 1 ≤ rf := by linarith
      obtain ⟨rs, hrs, hmax⟩ := isCompact_Icc.exists_isMaxOn
        (Set.nonempty_Icc.2 hr0rf) (Pi_cont (a := a) (φ := φ) (c := c) (rf := rf) hr0)
      have hrs1 : -1 < rs := by linarith [hrs.1]
      refine ⟨rs, hrs1, hrs.2, ?_⟩
      intro r hr1 hr2
      rw [hPi r hr1 hr2, hPi rs hrs1 hrs.2]
      have hrfmax : Pi a φ c rf rf ≤ Pi a φ c rf rs := hmax ⟨hr0rf, le_rfl⟩
      by_cases hlow : r < s0 - 1
      · have hsK : (1 + r) * K' < a ^ 2 * (1 - φ) ^ 3 := by
          have : 1 + r < a ^ 2 * (1 - φ) ^ 3 / K' := by linarith
          rwa [lt_div_iff₀ hK'pos] at this
        have hN : 0 < Nf a φ c rf r := by
          unfold Nf
          have hle : (1 + r) * (2 * a * c * (1 - φ) * φ + (1 + rf) * c ^ 2 * φ
              + c ^ 2 * (2 - φ) * (1 + r)) ≤ (1 + r) * K' := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            nlinarith [mul_le_mul_of_nonneg_left (show 1 + r ≤ 1 + rf by linarith) hc2.le, hK']
          nlinarith
        have := Pi_diff (a := a) (c := c) hk hR hr1
        have : 0 < (rf - r) * Nf a φ c rf r / (16 * (1 - φ) ^ 2 * (1 + r)) :=
          div_pos (mul_pos (by linarith) hN) (hden r hr1)
        linarith
      · push Not at hlow
        exact hmax ⟨hlow, hr2⟩
    · intro rs hrs1 hrs2 hmax
      rcases lt_or_eq_of_le hrs2 with h | h
      · exact h
      exfalso
      rw [h] at hmax
      obtain ⟨K, hK⟩ : ∃ K, K = 2 * a * c * (1 - φ) * φ + (1 + rf) * c ^ 2 * φ + 2 * c ^ 2 * (2 - φ) * (1 + rf) :=
        ⟨_, rfl⟩
      have hKpos : 0 < K := by
        have : 0 < 2 * c ^ 2 * (2 - φ) * (1 + rf) := by nlinarith [mul_pos hc2 hR]
        linarith
      obtain ⟨ε, hε⟩ : ∃ ε, ε = min ((1 + rf) / 2) (-(Nf a φ c rf rf) / (2 * K)) := ⟨_, rfl⟩
      have hεpos : 0 < ε := by
        subst hε; exact lt_min (by linarith) (div_pos (by linarith) (by linarith))
      have hε1 : ε ≤ (1 + rf) / 2 := by subst hε; exact min_le_left _ _
      have hε2 : ε ≤ -(Nf a φ c rf rf) / (2 * K) := by subst hε; exact min_le_right _ _
      have hεK : ε * K ≤ -(Nf a φ c rf rf) / 2 := by
        rw [le_div_iff₀ (by linarith)] at hε2
        nlinarith
      have hr1 : -1 < rf - ε := by linarith
      have hr2 : rf - ε ≤ rf := by linarith
      have hN : Nf a φ c rf (rf - ε) < 0 := by
        have e := N_expand a φ c rf (rf - ε)
        have hle : ε * (2 * a * c * (1 - φ) * φ + (1 + rf) * c ^ 2 * φ
            + c ^ 2 * (2 - φ) * ((1 + rf) + (1 + (rf - ε)))) ≤ ε * K := by
          apply mul_le_mul_of_nonneg_left _ hεpos.le
          linarith [mul_le_mul_of_nonneg_left (show 1 + (rf - ε) ≤ 1 + rf by linarith) hc2.le, hK]
        linarith
      have hd := Pi_diff (a := a) (c := c) hk hR hr1
      have hneg : (rf - (rf - ε)) * Nf a φ c rf (rf - ε) / (16 * (1 - φ) ^ 2 * (1 + (rf - ε)))
          < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) hN) (hden _ hr1)
      have hm := hmax (rf - ε) hr1 hr2
      rw [hPi _ hr1 hr2, hPi rf (by linarith) le_rfl] at hm
      linarith

end

end PlatformFinance.EndogRate


-- Platform entry point: restates the target verbatim.
namespace PlatformFinance.EndogRate

/-- Proposition 8 (p. 22): for `δ ≤ δ2`, the platform choosing its loan rate `r` subject to the
seller's participation `r ≤ r̂1(δ)` (and `r > -1`), with the stage-2 game played in a
subgame-perfect equilibrium `σP r` at every feasible `r`, sets `r* = rf` (the unique optimum)
if `c ≤ a(1 - φ)²/(1 + rf)`, and an optimal rate exists and every optimal rate is `< rf` if
`c > a(1 - φ)²/(1 + rf)`. -/
theorem _root_.solution (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (hδ2 : δ ≤ delta2 a φ c rf)
    (σP : ℝ → Profile)
    (hP : ∀ r : ℝ, -1 < r → r ≤ rhat1 a δ φ c rf → IsSPEP a δ φ c rf r (σP r)) :
    (c ≤ cbar a φ rf →
      -1 < rf ∧ rf ≤ rhat1 a δ φ c rf ∧
        ∀ r : ℝ, -1 < r → r ≤ rhat1 a δ φ c rf → r ≠ rf →
          platformProfitP a δ φ rf r (σP r) < platformProfitP a δ φ rf rf (σP rf)) ∧
    (cbar a φ rf < c →
      (∃ rs : ℝ, -1 < rs ∧ rs ≤ rhat1 a δ φ c rf ∧
        ∀ r : ℝ, -1 < r → r ≤ rhat1 a δ φ c rf →
          platformProfitP a δ φ rf r (σP r) ≤ platformProfitP a δ φ rf rs (σP rs)) ∧
      ∀ rs : ℝ, -1 < rs → rs ≤ rhat1 a δ φ c rf →
        (∀ r : ℝ, -1 < r → r ≤ rhat1 a δ φ c rf →
          platformProfitP a δ φ rf r (σP r) ≤ platformProfitP a δ φ rf rs (σP rs)) →
        rs < rf) := by
  apply @PlatformFinance.EndogRate.proposition_8 <;> assumption

end PlatformFinance.EndogRate
