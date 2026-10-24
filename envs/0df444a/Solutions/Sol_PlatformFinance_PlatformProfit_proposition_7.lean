-- Prove2me | solution 1 for PlatformFinance.PlatformProfit.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T19:07:00.295301+00:00
-- url     : https://prove2.me/submissions/c099011f-30a4-47be-94cf-0a6800619bb7

import Mathlib
import Definitions.Def_PlatformFinance_PlatformProfit_Model

/-!
Proposition 7 (Huang, Lai, Wang & Xiao, p. 19; proof p. 41). The trade-credit and
platform-financing equilibria are characterised as in Propositions 1-3 (namespaces PFWT, PFWP,
PFW3). For `δ ≤ δ₂` both are in the low-uncertainty regime, the seller never defaults under
platform financing, and the profit difference factors as
`(r - r_f) * E(1+r) / (16(1-φ)²(1+r))` with `4(2-φ)E(1+r) = 2c(2-φ)(r₆ - r)(√Δ + B + 2(2-φ)c(1+r))`.
-/

set_option autoImplicit false

namespace PFWT
open PlatformFinance.WinWin

lemma int_xsub (lo hi t : ℝ) : ∫ x in lo..hi, (x - t) = ((hi - t) ^ 2 - (lo - t) ^ 2) / 2 := by
  rw [show (∫ x in lo..hi, (x - t)) = ∫ x in lo - t..hi - t, x from
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x) t, integral_id]

lemma intpos (lo hi t : ℝ) (h : lo ≤ hi) :
    ∫ x in lo..hi, max (x - t) 0 = (max (hi - t) 0 ^ 2 - max (lo - t) 0 ^ 2) / 2 := by
  rcases le_total t lo with h1 | h1
  · have e : ∫ x in lo..hi, max (x - t) 0 = ∫ x in lo..hi, (x - t) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le h] at hx
      simp only
      rw [max_eq_left (by linarith [hx.1])]
    rw [e, int_xsub, max_eq_left (by linarith), max_eq_left (by linarith)]
  · rcases le_total hi t with h2 | h2
    · have e : ∫ x in lo..hi, max (x - t) 0 = ∫ x in lo..hi, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le h] at hx
        simp only
        rw [max_eq_right (by linarith [hx.2])]
      rw [e, intervalIntegral.integral_zero, max_eq_right (by linarith),
        max_eq_right (by linarith)]
      ring
    · have hc : Continuous (fun x : ℝ => max (x - t) 0) := by fun_prop
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := t) (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
      have e1 : ∫ x in lo..t, max (x - t) 0 = ∫ x in lo..t, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le h1] at hx
        simp only
        rw [max_eq_right (by linarith [hx.2])]
      have e2 : ∫ x in t..hi, max (x - t) 0 = ∫ x in t..hi, (x - t) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le h2] at hx
        simp only
        rw [max_eq_left (by linarith [hx.1])]
      rw [e1, e2, intervalIntegral.integral_zero, int_xsub, max_eq_left (by linarith),
        max_eq_right (by linarith)]
      ring

lemma seller_cf (a δ φ W q : ℝ) (hδ : 0 < δ) (hk : 0 < 1 - φ) (hq : 0 ≤ q) :
    sellerPayoff a δ φ W q = (1 - φ) * q *
      (max (a + δ - (q + W / (1 - φ))) 0 ^ 2 - max (a - δ - (q + W / (1 - φ))) 0 ^ 2)
        / (4 * δ) := by
  unfold sellerPayoff uniformMean
  have hkq : 0 ≤ (1 - φ) * q := by positivity
  have e : ∀ x : ℝ, max ((1 - φ) * (x - q) * q - W * q) 0
      = ((1 - φ) * q) * max (x - (q + W / (1 - φ))) 0 := by
    intro x
    rw [mul_max_of_nonneg _ _ hkq, mul_zero]
    congr 1
    field_simp
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intpos _ _ _ (by linarith)]
  field_simp
  ring

lemma seller_cf2 (a δ φ W q b : ℝ) (hδ : 0 < δ) (hk : 0 < 1 - φ) (hq : 0 ≤ q)
    (hb : a + δ - W / (1 - φ) = b) :
    sellerPayoff a δ φ W q
      = (1 - φ) / (4 * δ) * (q * (max (b - q) 0 ^ 2 - max (b - 2 * δ - q) 0 ^ 2)) := by
  rw [seller_cf a δ φ W q hδ hk hq, show a + δ - (q + W / (1 - φ)) = b - q by rw [← hb]; ring,
    show a - δ - (q + W / (1 - φ)) = b - 2 * δ - q by rw [← hb]; ring]
  ring

lemma supp_eq (a δ φ c rf w q : ℝ) (hδ : 0 < δ) :
    supplierPayoffT a δ φ c rf w q
      = (1 - φ) * (a - q) * q - sellerPayoff a δ φ w q - c * q * (1 + rf) := by
  unfold supplierPayoffT sellerPayoff uniformMean
  have e : ∀ x : ℝ, min ((1 - φ) * (x - q) * q) (w * q)
      = (1 - φ) * q * (x - q) - max ((1 - φ) * (x - q) * q - w * q) 0 := by
    intro x
    rcases le_total ((1 - φ) * (x - q) * q) (w * q) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  simp_rw [e]
  have hc1 : Continuous (fun x : ℝ => max ((1 - φ) * (x - q) * q - w * q) 0) := by fun_prop
  have hc2 : Continuous (fun x : ℝ => (1 - φ) * q * (x - q)) := by fun_prop
  rw [show (∫ x in a - δ..a + δ, ((1 - φ) * q * (x - q) - max ((1 - φ) * (x - q) * q - w * q) 0))
      = (∫ x in a - δ..a + δ, (1 - φ) * q * (x - q))
        - ∫ x in a - δ..a + δ, max ((1 - φ) * (x - q) * q - w * q) 0 from
      intervalIntegral.integral_sub (hc2.intervalIntegrable _ _) (hc1.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, int_xsub]
  field_simp
  ring

/-! Lemma 1 in normalised form: `g(q) = q((b-q)⁺² - (b-2δ-q)⁺²)`. -/

lemma gA0 (b δ : ℝ) (h3 : 3 * δ ≤ b) (hδ : 0 < δ) :
    (b - δ) / 2 * (max (b - (b - δ) / 2) 0 ^ 2 - max (b - 2 * δ - (b - δ) / 2) 0 ^ 2)
      = δ * (b - δ) ^ 2 := by
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring

lemma gB0 (b δ : ℝ) (hb : 0 < b) (h3 : b < 3 * δ) :
    b / 3 * (max (b - b / 3) 0 ^ 2 - max (b - 2 * δ - b / 3) 0 ^ 2) = 4 * b ^ 3 / 27 := by
  rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring

lemma gA (b δ q : ℝ) (hδ : 0 < δ) (h3 : 3 * δ ≤ b) (hq : 0 ≤ q) (hne : ¬ q = (b - δ) / 2) :
    q * (max (b - q) 0 ^ 2 - max (b - 2 * δ - q) 0 ^ 2) < δ * (b - δ) ^ 2 := by
  rcases le_or_gt q (b - 2 * δ) with h1 | h1
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    have hne' : b - δ - 2 * q ≠ 0 := fun h => hne (by linarith)
    have : 0 < (b - δ - 2 * q) ^ 2 := by positivity
    nlinarith [mul_pos hδ this]
  · rcases le_or_gt q b with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      have hr1 : 0 < 2 * δ - (b - q) := by linarith
      have hr0 : 0 ≤ b - q := by linarith
      nlinarith [mul_nonneg hδ.le (sq_nonneg (b - 3 * δ)),
        mul_nonneg hr1.le (mul_nonneg (show 0 ≤ b - 3 * δ by linarith)
          (show 0 ≤ 2 * δ + (b - q) by linarith)),
        mul_pos (mul_pos hr1 hr1) (show 0 < δ + (b - q) by linarith)]
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      have : 0 < (b - δ) ^ 2 := pow_pos (by linarith) 2
      nlinarith [mul_pos hδ this]

lemma gB (b δ q : ℝ) (hδ : 0 < δ) (hb : 0 < b) (h3 : b < 3 * δ) (hq : 0 ≤ q)
    (hne : ¬ q = b / 3) :
    q * (max (b - q) 0 ^ 2 - max (b - 2 * δ - q) 0 ^ 2) < 4 * b ^ 3 / 27 := by
  rcases le_or_gt q (b - 2 * δ) with h1 | h1
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    have p1 : 0 ≤ δ * ((b - 2 * δ - q) * (δ - q)) :=
      mul_nonneg hδ.le (mul_nonneg (by linarith) (by linarith))
    have p2 : 0 < (3 * δ - b) ^ 2 * (b + 6 * δ) := mul_pos (pow_pos (by linarith) 2) (by linarith)
    nlinarith
  · rcases le_or_gt q b with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      have hne' : 3 * q - b ≠ 0 := fun h => hne (by linarith)
      have p : 0 < (3 * q - b) ^ 2 * (4 * b - 3 * q) :=
        mul_pos (by positivity) (by linarith)
      nlinarith
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      have : 0 < b ^ 3 := pow_pos hb 3
      nlinarith

/-- The seller's rule orders the unique maximiser (Lemma 1), or `0` when nothing is profitable. -/
lemma order_eq (a δ φ w b : ℝ) (order : ℝ → ℝ) (hδ : 0 < δ) (hk : 0 < 1 - φ)
    (hR : IsSellerRule a δ φ (fun w => w) order) (hb : a + δ - w / (1 - φ) = b) :
    (0 < b → order w = (if 3 * δ ≤ b then (b - δ) / 2 else b / 3)) ∧
      (b ≤ 0 → order w = 0) := by
  have hR' : ∀ w : ℝ, 0 ≤ order w ∧
      (∀ q : ℝ, 0 ≤ q → sellerPayoff a δ φ w q ≤ sellerPayoff a δ φ w (order w)) ∧
      ((∀ q : ℝ, 0 ≤ q → sellerPayoff a δ φ w q ≤ 0) → order w = 0) := hR
  obtain ⟨h0, hmax, htie⟩ := hR' w
  have hc : 0 < (1 - φ) / (4 * δ) := by positivity
  constructor
  · intro hbpos
    by_contra hne
    have hq0 : 0 ≤ (if 3 * δ ≤ b then (b - δ) / 2 else b / 3) := by
      split_ifs <;> linarith
    have h1 := hmax _ hq0
    rw [seller_cf2 a δ φ w _ b hδ hk hq0 hb, seller_cf2 a δ φ w _ b hδ hk h0 hb] at h1
    have h2 : order w * (max (b - order w) 0 ^ 2 - max (b - 2 * δ - order w) 0 ^ 2) <
        (if 3 * δ ≤ b then (b - δ) / 2 else b / 3) *
          (max (b - (if 3 * δ ≤ b then (b - δ) / 2 else b / 3)) 0 ^ 2 -
            max (b - 2 * δ - (if 3 * δ ≤ b then (b - δ) / 2 else b / 3)) 0 ^ 2) := by
      split_ifs at hne ⊢ with h3
      · rw [gA0 b δ h3 hδ]; exact gA b δ (order w) hδ h3 h0 hne
      · rw [gB0 b δ hbpos (not_le.mp h3)]
        exact gB b δ (order w) hδ hbpos (not_le.mp h3) h0 hne
    have := mul_lt_mul_of_pos_left h2 hc
    linarith
  · intro hb0
    apply htie
    intro q hq
    rw [seller_cf2 a δ φ w q b hδ hk hq hb, max_eq_right (by linarith : b - q ≤ 0)]
    have : 0 ≤ q * max (b - 2 * δ - q) 0 ^ 2 := by positivity
    have h4 : q * ((0:ℝ) ^ 2 - max (b - 2 * δ - q) 0 ^ 2) ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos hc.le h4

/-- The supplier's objective in the normalised variable `b`, with `A = a - c(1+r_f)/(1-φ)`. -/
noncomputable def phiN (A δ b : ℝ) : ℝ :=
  if b ≤ 0 then 0
  else if b < 3 * δ then b * (9 * δ * A - 3 * δ * b - b ^ 2) / (27 * δ)
  else (b - δ) * (A + δ - b) / 2

lemma Phi_eq (a δ φ c rf w : ℝ) (order : ℝ → ℝ) (hδ : 0 < δ) (hk : 0 < 1 - φ)
    (hR : IsSellerRule a δ φ (fun w => w) order) :
    supplierPayoffT a δ φ c rf w (order w)
      = (1 - φ) * phiN (a - c * (1 + rf) / (1 - φ)) δ (a + δ - w / (1 - φ)) := by
  obtain ⟨b, hb⟩ : ∃ b, a + δ - w / (1 - φ) = b := ⟨_, rfl⟩
  rw [hb]
  have ho := order_eq a δ φ w b order hδ hk hR hb
  unfold phiN
  rcases le_or_gt b 0 with h0 | h0
  · rw [if_pos h0, ho.2 h0, supp_eq a δ φ c rf w 0 hδ,
      seller_cf2 a δ φ w 0 b hδ hk le_rfl hb]
    ring
  · rw [if_neg (not_le.mpr h0), ho.1 h0, supp_eq a δ φ c rf w _ hδ]
    rcases le_or_gt (3 * δ) b with h3 | h3
    · rw [if_neg (not_lt.mpr h3), if_pos h3,
        seller_cf2 a δ φ w _ b hδ hk (by linarith) hb, gA0 b δ h3 hδ]
      field_simp
      ring
    · rw [if_pos h3, if_neg (not_le.mpr h3),
        seller_cf2 a δ φ w _ b hδ hk (by linarith) hb, gB0 b δ h0 h3]
      field_simp
      ring

lemma phiI (A δ S b : ℝ) (hδ : 0 < δ) (hS : 1 < S) (hA : A = δ * (S ^ 2 - 1) / 3)
    (hI : 0 ≤ 3 * S ^ 2 - 10 * S - 5) :
    phiN A δ b ≤ A ^ 2 / 8 ∧ (A / 2 + δ < b → phiN A δ b < A ^ 2 / 8) := by
  have hS37 : 3.7 ≤ S := by nlinarith
  have hA4 : 4 * δ ≤ A := by
    rw [hA]; nlinarith [mul_nonneg hδ.le (show (0:ℝ) ≤ S ^ 2 - 13 by nlinarith)]
  unfold phiN
  split_ifs with h0 h3
  · exact ⟨by positivity, fun hb => by linarith⟩
  · have hb0 : 0 < b := not_le.mp h0
    have e1 : δ ^ 3 * (S - 1) ^ 2 * (2 * S + 1) - b * (9 * δ * A - 3 * δ * b - b ^ 2)
        = (b - δ * (S - 1)) ^ 2 * (b + (2 * S + 1) * δ) := by rw [hA]; ring
    have e2 : 27 * δ * A ^ 2 - 8 * (δ ^ 3 * (S - 1) ^ 2 * (2 * S + 1))
        = δ ^ 3 * (S - 1) ^ 2 * (3 * S ^ 2 - 10 * S - 5) := by rw [hA]; ring
    have p1 : 0 ≤ (b - δ * (S - 1)) ^ 2 * (b + (2 * S + 1) * δ) :=
      mul_nonneg (sq_nonneg _) (by nlinarith)
    have p2 : 0 ≤ δ ^ 3 * (S - 1) ^ 2 * (3 * S ^ 2 - 10 * S - 5) :=
      mul_nonneg (by positivity) hI
    constructor
    · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    · intro hb; linarith
  · constructor
    · nlinarith [sq_nonneg (A + 2 * δ - 2 * b)]
    · intro hb; nlinarith [pow_pos (show 0 < 2 * b - A - 2 * δ by linarith) 2]

lemma phiI_val (A δ : ℝ) (hδ : 0 < δ) (hA4 : 4 * δ ≤ A) :
    phiN A δ (A / 2 + δ) = A ^ 2 / 8 := by
  unfold phiN
  rw [if_neg (by linarith), if_neg (by linarith)]
  ring

lemma phiII (A δ S b : ℝ) (hδ : 0 < δ) (hS : 1 < S) (hA : A = δ * (S ^ 2 - 1) / 3)
    (hII : 3 * S ^ 2 - 10 * S - 5 < 0) :
    phiN A δ b ≤ δ ^ 2 * (S - 1) ^ 2 * (2 * S + 1) / 27 ∧
      (δ * (S - 1) < b → phiN A δ b < δ ^ 2 * (S - 1) ^ 2 * (2 * S + 1) / 27) := by
  have hS4 : S < 4 := by nlinarith
  have hpos : 0 < δ ^ 2 * (S - 1) ^ 2 * (2 * S + 1) / 27 :=
    div_pos (mul_pos (mul_pos (by positivity) (pow_pos (by linarith) 2)) (by linarith))
      (by norm_num)
  unfold phiN
  split_ifs with h0 h3
  · exact ⟨hpos.le, fun _ => hpos⟩
  · have hb0 : 0 < b := not_le.mp h0
    have e1 : δ ^ 3 * (S - 1) ^ 2 * (2 * S + 1) - b * (9 * δ * A - 3 * δ * b - b ^ 2)
        = (b - δ * (S - 1)) ^ 2 * (b + (2 * S + 1) * δ) := by rw [hA]; ring
    have p1 : 0 ≤ (b - δ * (S - 1)) ^ 2 * (b + (2 * S + 1) * δ) :=
      mul_nonneg (sq_nonneg _) (by nlinarith)
    constructor
    · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    · intro hb
      have p1' : 0 < (b - δ * (S - 1)) ^ 2 * (b + (2 * S + 1) * δ) :=
        mul_pos (pow_pos (by linarith) 2) (by nlinarith)
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · have h3' : 3 * δ ≤ b := not_lt.mp h3
    have hlt : (b - δ) * (A + δ - b) / 2 < δ ^ 2 * (S - 1) ^ 2 * (2 * S + 1) / 27 := by
      have e3 : δ ^ 2 * (S - 1) ^ 2 * (2 * S + 1) / 27 - δ * (A - 2 * δ)
          = δ ^ 2 * (4 - S) ^ 2 * (2 * S + 4) / 27 := by rw [hA]; ring
      have q3 : 0 < δ ^ 2 * (4 - S) ^ 2 * (2 * S + 4) / 27 :=
        div_pos (mul_pos (mul_pos (by positivity) (pow_pos (by linarith) 2)) (by linarith))
          (by norm_num)
      rcases le_or_gt A (4 * δ) with hA4 | hA4
      · nlinarith [mul_nonneg (show 0 ≤ b - 3 * δ by linarith)
          (show 0 ≤ b + δ - A by linarith)]
      · have e4 : δ ^ 2 * (S - 1) ^ 2 * (2 * S + 1) / 27 - A ^ 2 / 8
            = δ ^ 2 * (S - 1) ^ 2 * (-(3 * S ^ 2 - 10 * S - 5)) / 216 := by rw [hA]; ring
        have q4 : 0 < δ ^ 2 * (S - 1) ^ 2 * (-(3 * S ^ 2 - 10 * S - 5)) / 216 :=
          div_pos (mul_pos (mul_pos (by positivity) (pow_pos (by linarith) 2)) (by linarith))
            (by norm_num)
        nlinarith [sq_nonneg (A + 2 * δ - 2 * b)]
    exact ⟨hlt.le, fun _ => hlt⟩

lemma phiII_val (A δ S : ℝ) (hδ : 0 < δ) (hS : 1 < S) (hS4 : S < 4)
    (hA : A = δ * (S ^ 2 - 1) / 3) :
    phiN A δ (δ * (S - 1)) = δ ^ 2 * (S - 1) ^ 2 * (2 * S + 1) / 27 := by
  unfold phiN
  rw [if_neg (by nlinarith), if_pos (by nlinarith), hA]
  field_simp
  ring

/-- Least-maximiser argument. -/
lemma sup_char (Φ f : ℝ → ℝ) (k bstar val w0 w : ℝ) (hk : 0 < k)
    (hΦ : ∀ v, Φ v = k * f (bstar + (w0 - v) / k)) (hle : ∀ b, f b ≤ val)
    (hlt : ∀ b, bstar < b → f b < val) (hval : f bstar = val)
    (h2 : Φ w0 ≤ Φ w) (h3 : w0 < w → Φ w0 < Φ w) : w = w0 ∧ Φ w0 = k * val := by
  have hΦ0 : Φ w0 = k * val := by rw [hΦ, sub_self, zero_div, add_zero, hval]
  refine ⟨?_, hΦ0⟩
  rcases lt_trichotomy w w0 with h | h | h
  · exfalso
    have hpos : 0 < (w0 - w) / k := div_pos (by linarith) hk
    have := hlt _ (show bstar < bstar + (w0 - w) / k by linarith)
    have := mul_lt_mul_of_pos_left this hk
    rw [hΦ w] at h2
    linarith
  · exact h
  · exfalso
    have := h3 h
    rw [hΦ w] at this
    have := mul_le_mul_of_nonneg_left (hle (bstar + (w0 - w) / k)) hk.le
    linarith

lemma sqrt10_gt3 : (3:ℝ) < Real.sqrt 10 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma S_facts (a δ φ c rf : ℝ) (hδ : 0 < δ) (hφ1 : φ < 1) (hK : 0 < K0 a φ c rf) :
    δ * (1 - φ) * Sroot a δ φ c rf ^ 2 = (δ + 3 * a) * (1 - φ) - 3 * c * (1 + rf) ∧
      1 < Sroot a δ φ c rf ∧
      Kfun a δ φ c rf = δ * (1 - φ) * (Sroot a δ φ c rf - 1) ^ 2 * (2 * Sroot a δ φ c rf + 1) := by
  unfold K0 at hK
  have hk : 0 < 1 - φ := by linarith
  have hdk : 0 < δ * (1 - φ) := by positivity
  set X := (δ + 3 * a) * (1 - φ) - 3 * c * (1 + rf) with hXdef
  have hX : δ * (1 - φ) < X := by rw [hXdef]; nlinarith
  have hq : 1 < X / (δ * (1 - φ)) := by rw [lt_div_iff₀ hdk]; linarith
  have hS2 : Sroot a δ φ c rf ^ 2 = X / (δ * (1 - φ)) := by
    unfold Sroot; rw [Real.sq_sqrt (by linarith)]
  have h1 : δ * (1 - φ) * Sroot a δ φ c rf ^ 2 = X := by
    rw [hS2]; field_simp
  refine ⟨h1, ?_, ?_⟩
  · unfold Sroot; rw [Real.lt_sqrt (by norm_num)]; linarith
  · have hS0 : 0 ≤ Sroot a δ φ c rf := Real.sqrt_nonneg _
    set S := Sroot a δ φ c rf with hSdef
    have e3 : X ^ 3 / (δ * (1 - φ)) = (δ * (1 - φ) * S ^ 3) ^ 2 := by
      rw [← h1]; field_simp
    unfold Kfun
    rw [← hXdef, e3, Real.sqrt_sq (by positivity)]
    linear_combination 3 * h1

lemma S_case (a δ φ c rf : ℝ) (hδ : 0 < δ) (hφ1 : φ < 1) (hK : 0 < K0 a φ c rf) :
    (δ ≤ delta1 a φ c rf → 0 ≤ 3 * Sroot a δ φ c rf ^ 2 - 10 * Sroot a δ φ c rf - 5) ∧
    (delta1 a φ c rf < δ → 3 * Sroot a δ φ c rf ^ 2 - 10 * Sroot a δ φ c rf - 5 < 0) := by
  have hk : 0 < 1 - φ := by linarith
  obtain ⟨hS1, hS, -⟩ := S_facts a δ φ c rf hδ hφ1 hK
  have ht0 := sqrt10_gt3
  have ht : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  unfold delta1
  set S := Sroot a δ φ c rf
  set t := Real.sqrt 10
  have h3K : 3 * K0 a φ c rf = δ * (1 - φ) * (S ^ 2 - 1) := by
    unfold K0; linear_combination -hS1
  have hd1 : (5 * t - 14) * K0 a φ c rf / (8 * (1 - φ)) = (5 * t - 14) * (δ * (S ^ 2 - 1)) / 24 := by
    rw [div_eq_div_iff (by positivity) (by norm_num)]
    linear_combination 8 * (5 * t - 14) * h3K
  have h54 : (5 * t - 14) * (5 * t + 14) = 54 := by linear_combination 25 * ht
  have hfac : 3 * (3 * S ^ 2 - 10 * S - 5) = (3 * S - 5 - 2 * t) * (3 * S - 5 + 2 * t) := by
    linear_combination 4 * ht
  have hsq : (5 + 2 * t) ^ 2 = 65 + 20 * t := by linear_combination 4 * ht
  rw [hd1]
  constructor
  · intro hd
    have hx : 24 * δ ≤ (5 * t - 14) * (S ^ 2 - 1) * δ := by linarith
    have hx' : 24 ≤ (5 * t - 14) * (S ^ 2 - 1) := le_of_mul_le_mul_right hx hδ
    have hy : 24 * (5 * t + 14) ≤ 54 * (S ^ 2 - 1) := by
      have := mul_le_mul_of_nonneg_left hx' (show (0:ℝ) ≤ 5 * t + 14 by linarith)
      calc 24 * (5 * t + 14) = (5 * t + 14) * 24 := by ring
        _ ≤ (5 * t + 14) * ((5 * t - 14) * (S ^ 2 - 1)) := this
        _ = 54 * (S ^ 2 - 1) := by linear_combination (S ^ 2 - 1) * h54
    have hz : 5 + 2 * t ≤ 3 * S := by nlinarith
    have : 0 ≤ (3 * S - 5 - 2 * t) * (3 * S - 5 + 2 * t) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  · intro hd
    have hx : (5 * t - 14) * (S ^ 2 - 1) * δ < 24 * δ := by linarith
    have hx' : (5 * t - 14) * (S ^ 2 - 1) < 24 := lt_of_mul_lt_mul_right hx hδ.le
    have hy : 54 * (S ^ 2 - 1) < 24 * (5 * t + 14) := by
      have := mul_lt_mul_of_pos_left hx' (show (0:ℝ) < 5 * t + 14 by linarith)
      calc 54 * (S ^ 2 - 1) = (5 * t + 14) * ((5 * t - 14) * (S ^ 2 - 1)) := by
            linear_combination -(S ^ 2 - 1) * h54
        _ < (5 * t + 14) * 24 := this
        _ = 24 * (5 * t + 14) := by ring
    have hz : 3 * S < 5 + 2 * t := by nlinarith
    have : (3 * S - 5 - 2 * t) * (3 * S - 5 + 2 * t) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith

end PFWT

namespace PFWP
open PlatformFinance.WinWin

lemma int_xsub (lo hi t : ℝ) : ∫ x in lo..hi, (x - t) = ((hi - t) ^ 2 - (lo - t) ^ 2) / 2 := by
  rw [show (∫ x in lo..hi, (x - t)) = ∫ x in lo - t..hi - t, x from
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x) t, integral_id]

lemma intpos (lo hi t : ℝ) (h : lo ≤ hi) :
    ∫ x in lo..hi, max (x - t) 0 = (max (hi - t) 0 ^ 2 - max (lo - t) 0 ^ 2) / 2 := by
  rcases le_total t lo with h1 | h1
  · have e : ∫ x in lo..hi, max (x - t) 0 = ∫ x in lo..hi, (x - t) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le h] at hx
      simp only
      rw [max_eq_left (by linarith [hx.1])]
    rw [e, int_xsub, max_eq_left (by linarith), max_eq_left (by linarith)]
  · rcases le_total hi t with h2 | h2
    · have e : ∫ x in lo..hi, max (x - t) 0 = ∫ x in lo..hi, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le h] at hx
        simp only
        rw [max_eq_right (by linarith [hx.2])]
      rw [e, intervalIntegral.integral_zero, max_eq_right (by linarith),
        max_eq_right (by linarith)]
      ring
    · have hc : Continuous (fun x : ℝ => max (x - t) 0) := by fun_prop
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := t) (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
      have e1 : ∫ x in lo..t, max (x - t) 0 = ∫ x in lo..t, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le h1] at hx
        simp only
        rw [max_eq_right (by linarith [hx.2])]
      have e2 : ∫ x in t..hi, max (x - t) 0 = ∫ x in t..hi, (x - t) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le h2] at hx
        simp only
        rw [max_eq_left (by linarith [hx.1])]
      rw [e1, e2, intervalIntegral.integral_zero, int_xsub, max_eq_left (by linarith),
        max_eq_right (by linarith)]
      ring

lemma seller_cf (a δ φ W q : ℝ) (hδ : 0 < δ) (hk : 0 < 1 - φ) (hq : 0 ≤ q) :
    sellerPayoff a δ φ W q = (1 - φ) * q *
      (max (a + δ - (q + W / (1 - φ))) 0 ^ 2 - max (a - δ - (q + W / (1 - φ))) 0 ^ 2)
        / (4 * δ) := by
  unfold sellerPayoff uniformMean
  have hkq : 0 ≤ (1 - φ) * q := by positivity
  have e : ∀ x : ℝ, max ((1 - φ) * (x - q) * q - W * q) 0
      = ((1 - φ) * q) * max (x - (q + W / (1 - φ))) 0 := by
    intro x
    rw [mul_max_of_nonneg _ _ hkq, mul_zero]
    congr 1
    field_simp
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intpos _ _ _ (by linarith)]
  field_simp
  ring

lemma seller_cf2 (a δ φ W q b : ℝ) (hδ : 0 < δ) (hk : 0 < 1 - φ) (hq : 0 ≤ q)
    (hb : a + δ - W / (1 - φ) = b) :
    sellerPayoff a δ φ W q
      = (1 - φ) / (4 * δ) * (q * (max (b - q) 0 ^ 2 - max (b - 2 * δ - q) 0 ^ 2)) := by
  rw [seller_cf a δ φ W q hδ hk hq, show a + δ - (q + W / (1 - φ)) = b - q by rw [← hb]; ring,
    show a - δ - (q + W / (1 - φ)) = b - 2 * δ - q by rw [← hb]; ring]
  ring

/-! Lemma 1 in normalised form: `g(q) = q((b-q)⁺² - (b-2δ-q)⁺²)`. -/

lemma gA0 (b δ : ℝ) (h3 : 3 * δ ≤ b) (hδ : 0 < δ) :
    (b - δ) / 2 * (max (b - (b - δ) / 2) 0 ^ 2 - max (b - 2 * δ - (b - δ) / 2) 0 ^ 2)
      = δ * (b - δ) ^ 2 := by
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring

lemma gB0 (b δ : ℝ) (hb : 0 < b) (h3 : b < 3 * δ) :
    b / 3 * (max (b - b / 3) 0 ^ 2 - max (b - 2 * δ - b / 3) 0 ^ 2) = 4 * b ^ 3 / 27 := by
  rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring

lemma gA (b δ q : ℝ) (hδ : 0 < δ) (h3 : 3 * δ ≤ b) (hq : 0 ≤ q) (hne : ¬ q = (b - δ) / 2) :
    q * (max (b - q) 0 ^ 2 - max (b - 2 * δ - q) 0 ^ 2) < δ * (b - δ) ^ 2 := by
  rcases le_or_gt q (b - 2 * δ) with h1 | h1
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    have hne' : b - δ - 2 * q ≠ 0 := fun h => hne (by linarith)
    have : 0 < (b - δ - 2 * q) ^ 2 := by positivity
    nlinarith [mul_pos hδ this]
  · rcases le_or_gt q b with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      have hr1 : 0 < 2 * δ - (b - q) := by linarith
      have hr0 : 0 ≤ b - q := by linarith
      nlinarith [mul_nonneg hδ.le (sq_nonneg (b - 3 * δ)),
        mul_nonneg hr1.le (mul_nonneg (show 0 ≤ b - 3 * δ by linarith)
          (show 0 ≤ 2 * δ + (b - q) by linarith)),
        mul_pos (mul_pos hr1 hr1) (show 0 < δ + (b - q) by linarith)]
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      have : 0 < (b - δ) ^ 2 := pow_pos (by linarith) 2
      nlinarith [mul_pos hδ this]

lemma gB (b δ q : ℝ) (hδ : 0 < δ) (hb : 0 < b) (h3 : b < 3 * δ) (hq : 0 ≤ q)
    (hne : ¬ q = b / 3) :
    q * (max (b - q) 0 ^ 2 - max (b - 2 * δ - q) 0 ^ 2) < 4 * b ^ 3 / 27 := by
  rcases le_or_gt q (b - 2 * δ) with h1 | h1
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    have p1 : 0 ≤ δ * ((b - 2 * δ - q) * (δ - q)) :=
      mul_nonneg hδ.le (mul_nonneg (by linarith) (by linarith))
    have p2 : 0 < (3 * δ - b) ^ 2 * (b + 6 * δ) := mul_pos (pow_pos (by linarith) 2) (by linarith)
    nlinarith
  · rcases le_or_gt q b with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      have hne' : 3 * q - b ≠ 0 := fun h => hne (by linarith)
      have p : 0 < (3 * q - b) ^ 2 * (4 * b - 3 * q) :=
        mul_pos (by positivity) (by linarith)
      nlinarith
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      have : 0 < b ^ 3 := pow_pos hb 3
      nlinarith

/-- The seller's rule orders the unique maximiser (Lemma 1) for any owed amount. -/
lemma order_eqG (a δ φ : ℝ) (owed : ℝ → ℝ) (w b : ℝ) (order : ℝ → ℝ) (hδ : 0 < δ)
    (hk : 0 < 1 - φ) (hR : IsSellerRule a δ φ owed order) (hb : a + δ - owed w / (1 - φ) = b) :
    (0 < b → order w = (if 3 * δ ≤ b then (b - δ) / 2 else b / 3)) ∧
      (b ≤ 0 → order w = 0) := by
  obtain ⟨h0, hmax, htie⟩ := hR w
  have hc : 0 < (1 - φ) / (4 * δ) := by positivity
  constructor
  · intro hbpos
    by_contra hne
    have hq0 : 0 ≤ (if 3 * δ ≤ b then (b - δ) / 2 else b / 3) := by
      split_ifs <;> linarith
    have h1 := hmax _ hq0
    rw [seller_cf2 a δ φ (owed w) _ b hδ hk hq0 hb, seller_cf2 a δ φ (owed w) _ b hδ hk h0 hb] at h1
    have h2 : order w * (max (b - order w) 0 ^ 2 - max (b - 2 * δ - order w) 0 ^ 2) <
        (if 3 * δ ≤ b then (b - δ) / 2 else b / 3) *
          (max (b - (if 3 * δ ≤ b then (b - δ) / 2 else b / 3)) 0 ^ 2 -
            max (b - 2 * δ - (if 3 * δ ≤ b then (b - δ) / 2 else b / 3)) 0 ^ 2) := by
      split_ifs at hne ⊢ with h3
      · rw [gA0 b δ h3 hδ]; exact gA b δ (order w) hδ h3 h0 hne
      · rw [gB0 b δ hbpos (not_le.mp h3)]
        exact gB b δ (order w) hδ hbpos (not_le.mp h3) h0 hne
    have := mul_lt_mul_of_pos_left h2 hc
    linarith
  · intro hb0
    apply htie
    intro q hq
    rw [seller_cf2 a δ φ (owed w) q b hδ hk hq hb, max_eq_right (by linarith : b - q ≤ 0)]
    have : 0 ≤ q * max (b - 2 * δ - q) 0 ^ 2 := by positivity
    have h4 : q * ((0:ℝ) ^ 2 - max (b - 2 * δ - q) 0 ^ 2) ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos hc.le h4

/-- Supplier objective `(M - b) q(b)` in the normalised variable `b`, `M = a + δ - c(1+r)/(1-φ)`. -/
noncomputable def psi (M δ b : ℝ) : ℝ :=
  if b ≤ 0 then 0
  else if b < 3 * δ then (M - b) * b / 3
  else (M - b) * (b - δ) / 2

lemma PhiP_eq (a δ φ c rf r w M : ℝ) (order : ℝ → ℝ) (hδ : 0 < δ) (hk : 0 < 1 - φ)
    (hρ : 0 < 1 + r) (hR : IsSellerRule a δ φ (fun w => w * (1 + r)) order)
    (hM : M = a + δ - c * (1 + r) / (1 - φ)) :
    supplierPayoffP c rf w (order w)
      = ((1 + rf) * ((1 - φ) / (1 + r))) * psi M δ (a + δ - w * (1 + r) / (1 - φ)) := by
  obtain ⟨b, hb⟩ : ∃ b, a + δ - w * (1 + r) / (1 - φ) = b := ⟨_, rfl⟩
  have ho := order_eqG a δ φ (fun w => w * (1 + r)) w b order hδ hk hR hb
  have hw : w = (1 - φ) * (a + δ - b) / (1 + r) := by
    rw [← hb]; field_simp; ring
  rw [hb]
  unfold psi supplierPayoffP
  rcases le_or_gt b 0 with h0 | h0
  · rw [if_pos h0, ho.2 h0]; ring
  · rw [if_neg (not_le.mpr h0), ho.1 h0]
    rcases le_or_gt (3 * δ) b with h3 | h3
    · rw [if_pos h3, if_neg (not_lt.mpr h3), hw, hM]; field_simp; ring
    · rw [if_neg (not_le.mpr h3), if_pos h3, hw, hM]; field_simp; ring

lemma prod6 (M δ t : ℝ) (ht : t ^ 2 = 6) :
    (M - (3 + t) * δ) * (M - (3 - t) * δ) = M ^ 2 - 6 * M * δ + 3 * δ ^ 2 := by
  linear_combination (-δ ^ 2) * ht

lemma psiI (M δ t b : ℝ) (hδ : 0 < δ) (ht : t ^ 2 = 6) (ht2 : 2 < t)
    (hd : (3 + t) * δ ≤ M) :
    psi M δ b ≤ (M - δ) ^ 2 / 8 ∧ ((M + δ) / 2 < b → psi M δ b < (M - δ) ^ 2 / 8) := by
  have htd : 2 * δ < t * δ := mul_lt_mul_of_pos_right ht2 hδ
  have hM5 : 5 * δ < M := by nlinarith
  have hp : 0 ≤ (M - (3 + t) * δ) * (M - (3 - t) * δ) :=
    mul_nonneg (by linarith) (by nlinarith)
  rw [prod6 M δ t ht] at hp
  unfold psi
  split_ifs with h0 h3
  · exact ⟨by positivity, fun hb => by linarith⟩
  · constructor
    · nlinarith [sq_nonneg (M - 2 * b)]
    · intro hb; linarith
  · constructor
    · nlinarith [sq_nonneg (2 * b - M - δ)]
    · intro hb; nlinarith [pow_pos (show 0 < 2 * b - M - δ by linarith) 2]

lemma psiI_val (M δ : ℝ) (hδ : 0 < δ) (hM5 : 5 * δ ≤ M) :
    psi M δ ((M + δ) / 2) = (M - δ) ^ 2 / 8 := by
  unfold psi
  rw [if_neg (by linarith), if_neg (by linarith)]
  ring

lemma psiII (M δ t b : ℝ) (hδ : 0 < δ) (ht : t ^ 2 = 6) (ht0 : 0 < t) (ht3 : t < 3)
    (hM0 : 0 < M) (hd : M < (3 + t) * δ) :
    psi M δ b ≤ M ^ 2 / 12 ∧ (M / 2 < b → psi M δ b < M ^ 2 / 12) := by
  have htd : t * δ < 3 * δ := mul_lt_mul_of_pos_right ht3 hδ
  have htd0 : 0 < t * δ := mul_pos ht0 hδ
  have hM6 : M < 6 * δ := by linarith
  have hpos : 0 < M ^ 2 / 12 := by positivity
  unfold psi
  split_ifs with h0 h3
  · exact ⟨hpos.le, fun _ => hpos⟩
  · constructor
    · nlinarith [sq_nonneg (M - 2 * b)]
    · intro hb; nlinarith [pow_pos (show 0 < 2 * b - M by linarith) 2]
  · have h3' : 3 * δ ≤ b := not_lt.mp h3
    have hlt : (M - b) * (b - δ) / 2 < M ^ 2 / 12 := by
      rcases le_or_gt M (5 * δ) with h5 | h5
      · nlinarith [mul_nonneg (show 0 ≤ b - 3 * δ by linarith)
          (show 0 ≤ 30 * δ - 6 * M by linarith), sq_nonneg (b - 3 * δ),
          pow_pos (show 0 < 6 * δ - M by linarith) 2]
      · have hn : (M - (3 + t) * δ) * (M - (3 - t) * δ) < 0 :=
          mul_neg_of_neg_of_pos (by linarith) (by linarith)
        rw [prod6 M δ t ht] at hn
        nlinarith [sq_nonneg (2 * b - M - δ)]
    exact ⟨hlt.le, fun _ => hlt⟩

lemma psiII_val (M δ : ℝ) (hM0 : 0 < M) (hM6 : M < 6 * δ) :
    psi M δ (M / 2) = M ^ 2 / 12 := by
  unfold psi
  rw [if_neg (by linarith), if_pos (by linarith)]
  ring

/-- Least-maximiser argument with separate multiplier `m` and scale `s`. -/
lemma sup_char2 (Φ f : ℝ → ℝ) (m s bstar val w0 w : ℝ) (hm : 0 < m) (hs : 0 < s)
    (hΦ : ∀ v, Φ v = m * f (bstar + (w0 - v) * s)) (hle : ∀ b, f b ≤ val)
    (hlt : ∀ b, bstar < b → f b < val) (hval : f bstar = val)
    (h2 : Φ w0 ≤ Φ w) (h3 : w0 < w → Φ w0 < Φ w) : w = w0 ∧ Φ w0 = m * val := by
  have hΦ0 : Φ w0 = m * val := by rw [hΦ, sub_self, zero_mul, add_zero, hval]
  refine ⟨?_, hΦ0⟩
  rcases lt_trichotomy w w0 with h | h | h
  · exfalso
    have hpos : 0 < (w0 - w) * s := mul_pos (by linarith) hs
    have := hlt _ (show bstar < bstar + (w0 - w) * s by linarith)
    have := mul_lt_mul_of_pos_left this hm
    rw [hΦ w] at h2
    linarith
  · exact h
  · exfalso
    have := h3 h
    rw [hΦ w] at this
    have := mul_le_mul_of_nonneg_left (hle (bstar + (w0 - w) * s)) hm.le
    linarith

end PFWP

namespace PFW3
open PlatformFinance.WinWin

/-- Trade-credit equilibrium in terms of `bT = a + δ - w/(1-φ)` (Proposition 1). -/
lemma charT (a δ φ c rf : ℝ) (hδ : 0 < δ) (hφ1 : φ < 1) (hprof : c * (1 + rf) < (1 - φ) * a)
    (σ : Profile) (hσ : IsSPET a δ φ c rf σ) :
    σ.order σ.w = (if 3 * δ ≤ a + δ - σ.w / (1 - φ) then (a + δ - σ.w / (1 - φ) - δ) / 2
        else (a + δ - σ.w / (1 - φ)) / 3) ∧
    (δ ≤ delta1 a φ c rf → a + δ - σ.w / (1 - φ) = (a - c * (1 + rf) / (1 - φ)) / 2 + δ ∧
        4 * δ ≤ a - c * (1 + rf) / (1 - φ)) ∧
    (delta1 a φ c rf < δ → a + δ - σ.w / (1 - φ) = δ * (Sroot a δ φ c rf - 1) ∧
        Sroot a δ φ c rf < 4) := by
  have hk : 0 < 1 - φ := by linarith
  have hK : 0 < K0 a φ c rf := by unfold K0; linarith
  obtain ⟨hS1, hS, -⟩ := PFWT.S_facts a δ φ c rf hδ hφ1 hK
  obtain ⟨hcI, hcII⟩ := PFWT.S_case a δ φ c rf hδ hφ1 hK
  obtain ⟨hR, hmax, hlt⟩ := hσ
  have hPhi : ∀ w, supplierPayoffT a δ φ c rf w (σ.order w)
      = (1 - φ) * PFWT.phiN (a - c * (1 + rf) / (1 - φ)) δ (a + δ - w / (1 - φ)) :=
    fun w => PFWT.Phi_eq a δ φ c rf w σ.order hδ hk hR
  obtain ⟨A, hAdef⟩ : ∃ A, A = a - c * (1 + rf) / (1 - φ) := ⟨_, rfl⟩
  rw [← hAdef] at hPhi ⊢
  have hK0 : K0 a φ c rf = (1 - φ) * A := by
    rw [hAdef]; unfold K0; field_simp
  set S := Sroot a δ φ c rf with hSdef
  have hA : A = δ * (S ^ 2 - 1) / 3 := by
    have : 3 * ((1 - φ) * A) = δ * (1 - φ) * (S ^ 2 - 1) := by
      rw [← hK0]; unfold K0; linear_combination -hS1
    have h' : (1 - φ) * (3 * A) = (1 - φ) * (δ * (S ^ 2 - 1)) := by linear_combination this
    have := mul_left_cancel₀ (ne_of_gt hk) h'
    linarith
  by_cases hd : δ ≤ delta1 a φ c rf
  · have hI := hcI hd
    have hS37 : 3.7 ≤ S := by nlinarith
    have hA4 : 4 * δ ≤ A := by
      rw [hA]; nlinarith [mul_nonneg hδ.le (show (0:ℝ) ≤ S ^ 2 - 13 by nlinarith)]
    have hwT : wT a δ φ c rf = ((1 - φ) * a + c * (1 + rf)) / 2 := by
      unfold wT; rw [if_pos hd]
    have hbw : ∀ v, a + δ - v / (1 - φ) = (A / 2 + δ) + (wT a δ φ c rf - v) / (1 - φ) := by
      intro v; rw [hwT, hAdef]; field_simp; ring
    obtain ⟨hw, -⟩ := PFWT.sup_char (fun v => supplierPayoffT a δ φ c rf v (σ.order v))
      (PFWT.phiN A δ) (1 - φ) (A / 2 + δ) (A ^ 2 / 8) (wT a δ φ c rf) σ.w hk
      (fun v => by show supplierPayoffT a δ φ c rf v (σ.order v) = _; rw [hPhi, hbw])
      (fun b => (PFWT.phiI A δ S b hδ hS hA hI).1) (fun b => (PFWT.phiI A δ S b hδ hS hA hI).2)
      (PFWT.phiI_val A δ hδ hA4) (hmax _) (hlt _)
    have hbT : a + δ - wT a δ φ c rf / (1 - φ) = A / 2 + δ := by
      rw [hbw]; simp
    have hord := (PFWT.order_eq a δ φ (wT a δ φ c rf) (A / 2 + δ) σ.order hδ hk hR hbT).1
      (by linarith)
    have hb' : a + δ - σ.w / (1 - φ) = A / 2 + δ := by rw [hw]; exact hbT
    refine ⟨?_, fun _ => ⟨hb', hA4⟩, fun h => absurd hd (not_le.mpr h)⟩
    rw [hb', hw]; exact hord
  · have hII := hcII (not_le.mp hd)
    have hS4 : S < 4 := by nlinarith
    have hwT : wT a δ φ c rf = (1 - φ) * (a - δ * (S - 2)) := by
      unfold wT; rw [if_neg hd]
    have hbw : ∀ v, a + δ - v / (1 - φ) = δ * (S - 1) + (wT a δ φ c rf - v) / (1 - φ) := by
      intro v; rw [hwT]; field_simp; ring
    obtain ⟨hw, -⟩ := PFWT.sup_char (fun v => supplierPayoffT a δ φ c rf v (σ.order v))
      (PFWT.phiN A δ) (1 - φ) (δ * (S - 1)) (δ ^ 2 * (S - 1) ^ 2 * (2 * S + 1) / 27)
      (wT a δ φ c rf) σ.w hk
      (fun v => by show supplierPayoffT a δ φ c rf v (σ.order v) = _; rw [hPhi, hbw])
      (fun b => (PFWT.phiII A δ S b hδ hS hA hII).1)
      (fun b => fun hb => (PFWT.phiII A δ S b hδ hS hA hII).2 (by linarith))
      (PFWT.phiII_val A δ S hδ hS hS4 hA) (hmax _) (hlt _)
    have hbT : a + δ - wT a δ φ c rf / (1 - φ) = δ * (S - 1) := by
      rw [hbw]; simp
    have hb0 : 0 < δ * (S - 1) := mul_pos hδ (by linarith)
    have hord := (PFWT.order_eq a δ φ (wT a δ φ c rf) (δ * (S - 1)) σ.order hδ hk hR hbT).1 hb0
    have hb' : a + δ - σ.w / (1 - φ) = δ * (S - 1) := by rw [hw]; exact hbT
    refine ⟨?_, fun h => absurd h hd, fun _ => ⟨hb', hS4⟩⟩
    rw [hb', hw]; exact hord

/-- Platform-financing equilibrium in terms of `bP = a + δ - w(1+r)/(1-φ)` (Proposition 2). -/
lemma charP (a δ φ c rf r : ℝ) (hδ : 0 < δ) (hφ1 : φ < 1) (hrf : 0 ≤ rf) (hr : -1 < r)
    (hrq : c * (1 + r) < (a + δ) * (1 - φ)) (σ : Profile) (hσ : IsSPEP a δ φ c rf r σ) :
    σ.order σ.w = (if 3 * δ ≤ a + δ - σ.w * (1 + r) / (1 - φ)
        then (a + δ - σ.w * (1 + r) / (1 - φ) - δ) / 2
        else (a + δ - σ.w * (1 + r) / (1 - φ)) / 3) ∧
    ((3 + Real.sqrt 6) * δ ≤ a + δ - c * (1 + r) / (1 - φ) →
        a + δ - σ.w * (1 + r) / (1 - φ) = (a + δ - c * (1 + r) / (1 - φ) + δ) / 2) ∧
    (a + δ - c * (1 + r) / (1 - φ) < (3 + Real.sqrt 6) * δ →
        a + δ - σ.w * (1 + r) / (1 - φ) = (a + δ - c * (1 + r) / (1 - φ)) / 2) := by
  have hk : 0 < 1 - φ := by linarith
  have hρ : 0 < 1 + r := by linarith
  have hrf1 : 0 < 1 + rf := by linarith
  have hm : 0 < (1 + rf) * ((1 - φ) / (1 + r)) := by positivity
  have hs : 0 < (1 + r) / (1 - φ) := by positivity
  obtain ⟨hR, hmax, hlt⟩ := hσ
  obtain ⟨M, hMdef⟩ : ∃ M, M = a + δ - c * (1 + r) / (1 - φ) := ⟨_, rfl⟩
  rw [← hMdef]
  have hkM : (a + δ) * (1 - φ) - c * (1 + r) = (1 - φ) * M := by
    rw [hMdef]; field_simp
  have hM0 : 0 < M := by
    have : 0 < (1 - φ) * M := by rw [← hkM]; linarith
    nlinarith
  have hPhi : ∀ w, supplierPayoffP c rf w (σ.order w)
      = ((1 + rf) * ((1 - φ) / (1 + r))) * PFWP.psi M δ (a + δ - w * (1 + r) / (1 - φ)) :=
    fun w => PFWP.PhiP_eq a δ φ c rf r w M σ.order hδ hk hρ hR hMdef
  have ht : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have ht2 : 2 < Real.sqrt 6 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have ht3 : Real.sqrt 6 < 3 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  by_cases hd' : (3 + Real.sqrt 6) * δ ≤ M
  · have htd : 2 * δ < Real.sqrt 6 * δ := mul_lt_mul_of_pos_right ht2 hδ
    have hM5 : 5 * δ ≤ M := by linarith
    obtain ⟨ws, hws⟩ : ∃ ws, ws = (1 - φ) * (a + δ - (M + δ) / 2) / (1 + r) := ⟨_, rfl⟩
    have hbw : ∀ v, a + δ - v * (1 + r) / (1 - φ)
        = (M + δ) / 2 + (ws - v) * ((1 + r) / (1 - φ)) := by
      intro v; rw [hws]; field_simp; ring
    obtain ⟨hw, -⟩ := PFWP.sup_char2 (fun v => supplierPayoffP c rf v (σ.order v))
      (PFWP.psi M δ) ((1 + rf) * ((1 - φ) / (1 + r))) ((1 + r) / (1 - φ)) ((M + δ) / 2)
      ((M - δ) ^ 2 / 8) ws σ.w hm hs
      (fun v => by show supplierPayoffP c rf v (σ.order v) = _; rw [hPhi, hbw])
      (fun b => (PFWP.psiI M δ _ b hδ ht ht2 hd').1)
      (fun b => (PFWP.psiI M δ _ b hδ ht ht2 hd').2)
      (PFWP.psiI_val M δ hδ hM5) (hmax _) (hlt _)
    have hbT : a + δ - ws * (1 + r) / (1 - φ) = (M + δ) / 2 := by
      rw [hbw]; simp
    have hord := (PFWP.order_eqG a δ φ (fun w => w * (1 + r)) ws ((M + δ) / 2) σ.order hδ hk hR
      hbT).1 (by linarith)
    have hb' : a + δ - σ.w * (1 + r) / (1 - φ) = (M + δ) / 2 := by rw [hw]; exact hbT
    refine ⟨?_, fun _ => hb', fun h => absurd hd' (not_le.mpr h)⟩
    rw [hb', hw]; exact hord
  · have hd'' : M < (3 + Real.sqrt 6) * δ := lt_of_not_ge hd'
    have htd : Real.sqrt 6 * δ < 3 * δ := mul_lt_mul_of_pos_right ht3 hδ
    have hM6 : M < 6 * δ := by linarith
    obtain ⟨ws, hws⟩ : ∃ ws, ws = (1 - φ) * (a + δ - M / 2) / (1 + r) := ⟨_, rfl⟩
    have hbw : ∀ v, a + δ - v * (1 + r) / (1 - φ)
        = M / 2 + (ws - v) * ((1 + r) / (1 - φ)) := by
      intro v; rw [hws]; field_simp; ring
    obtain ⟨hw, -⟩ := PFWP.sup_char2 (fun v => supplierPayoffP c rf v (σ.order v))
      (PFWP.psi M δ) ((1 + rf) * ((1 - φ) / (1 + r))) ((1 + r) / (1 - φ)) (M / 2)
      (M ^ 2 / 12) ws σ.w hm hs
      (fun v => by show supplierPayoffP c rf v (σ.order v) = _; rw [hPhi, hbw])
      (fun b => (PFWP.psiII M δ _ b hδ ht (by linarith) ht3 hM0 hd'').1)
      (fun b => (PFWP.psiII M δ _ b hδ ht (by linarith) ht3 hM0 hd'').2)
      (PFWP.psiII_val M δ hM0 hM6) (hmax _) (hlt _)
    have hbT : a + δ - ws * (1 + r) / (1 - φ) = M / 2 := by
      rw [hbw]; simp
    have hord := (PFWP.order_eqG a δ φ (fun w => w * (1 + r)) ws (M / 2) σ.order hδ hk hR
      hbT).1 (by linarith)
    have hb' : a + δ - σ.w * (1 + r) / (1 - φ) = M / 2 := by rw [hw]; exact hbT
    refine ⟨?_, fun h => absurd h hd', fun _ => hb'⟩
    rw [hb', hw]; exact hord

/-- `δ ≤ δ₂` forces `δ ≤ δ₁` (in `S` coordinates). -/
lemma f_d2 (S t δ : ℝ) (hδ : 0 < δ) (ht1 : 2.449 < t) (hS : 1 < S)
    (h : δ * (t + 2) ≤ δ * (S ^ 2 - 1) / 3) (hneg : 3 * S ^ 2 - 10 * S - 5 < 0) : False := by
  have h' : 3 * (t + 2) ≤ S ^ 2 - 1 := by nlinarith
  have hSlt : S < 3.78 := by
    by_contra h2
    push Not at h2
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (show (0:ℝ) ≤ 3 * S + 1.34 by linarith)]
  nlinarith

/-- `δ ≤ δ₃` iff `S ≥ (5+√6)/2`: the `≤` direction. -/
lemma f_d3a (S t δ : ℝ) (hδ : 0 < δ) (ht : t ^ 2 = 6) (ht0 : 0 < t) (ht2 : t < 2.4495) (hS : 1 < S)
    (h : δ * 43 ≤ 4 * (27 - 10 * t) * (δ * (S ^ 2 - 1) / 3)) : (5 + t) / 2 ≤ S := by
  have h129 : (27 - 10 * t) * (27 + 10 * t) = 129 := by linear_combination -100 * ht
  have h5 : 129 ≤ 4 * (27 - 10 * t) * (S ^ 2 - 1) := by nlinarith
  have hp : 0 < 27 - 10 * t := by linarith
  have h7 : 27 + 10 * t ≤ 4 * (S ^ 2 - 1) := by
    by_contra hc
    push Not at hc
    nlinarith [mul_lt_mul_of_pos_left hc hp]
  by_contra hc
  push Not at hc
  nlinarith [mul_pos (sub_pos.2 hc) (show 0 < (5 + t) / 2 + S by linarith)]

/-- `δ > δ₃` gives `S < (5+√6)/2`. -/
lemma f_d3b (S t δ : ℝ) (hδ : 0 < δ) (ht : t ^ 2 = 6) (ht0 : 0 < t) (ht2 : t < 2.4495) (hS : 1 < S)
    (h : 4 * (27 - 10 * t) * (δ * (S ^ 2 - 1) / 3) < δ * 43) : S < (5 + t) / 2 := by
  have h129 : (27 - 10 * t) * (27 + 10 * t) = 129 := by linear_combination -100 * ht
  have h5 : 4 * (27 - 10 * t) * (S ^ 2 - 1) < 129 := by nlinarith
  have hp : 0 < 27 - 10 * t := by linarith
  have h7 : 4 * (S ^ 2 - 1) < 27 + 10 * t := by
    by_contra hc
    push Not at hc
    nlinarith [mul_le_mul_of_nonneg_left hc hp.le]
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg (sub_nonneg.2 hc) (show 0 ≤ (5 + t) / 2 + S by linarith)]

/-- `S < (5+√6)/2` is incompatible with `δ ≤ δ₁`. -/
lemma f_d1 (S t : ℝ) (hS : 1 < S) (ht2 : t < 2.4495) (h : S < (5 + t) / 2)
    (hpos : 0 ≤ 3 * S ^ 2 - 10 * S - 5) : False := by
  have h1 : S < 3.73 := by linarith
  nlinarith [mul_neg_of_neg_of_pos (show S - 3.73 < 0 by linarith)
    (show (0:ℝ) < 3 * S + 1.19 by linarith)]

lemma gmono (δ x y : ℝ) (hδ : 0 < δ) (h : x < y) :
    (if 3 * δ ≤ x then (x - δ) / 2 else x / 3) < (if 3 * δ ≤ y then (y - δ) / 2 else y / 3) := by
  split_ifs <;> linarith

lemma gmono' (δ x y : ℝ) (hδ : 0 < δ) (h : x ≤ y) :
    (if 3 * δ ≤ x then (x - δ) / 2 else x / 3) ≤ (if 3 * δ ≤ y then (y - δ) / 2 else y / 3) := by
  split_ifs <;> linarith

lemma sq_gt2 (S δ : ℝ) (hδ : 0 < δ) (hS : 1 < S) (h : δ < δ * (S ^ 2 - 1) / 3) : 2 < S := by
  have h1 : 4 < S ^ 2 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_le_mul_of_nonneg_left hc hδ.le]
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul hc hc (by linarith) (by norm_num : (0:ℝ) ≤ 2)]

lemma sq_lt2 (S δ : ℝ) (hδ : 0 < δ) (hS : 1 < S) (h : δ * (S ^ 2 - 1) / 3 < δ) : S < 2 := by
  have h1 : S ^ 2 < 4 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_le_mul_of_nonneg_left hc hδ.le]
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul hc hc (by norm_num : (0:ℝ) ≤ 2) (by linarith : (0:ℝ) ≤ S)]

end PFW3

namespace PFW7
open PlatformFinance.PlatformProfit

lemma int_lin (lo hi α β : ℝ) :
    ∫ x in lo..hi, (α * x + β) = α * ((hi ^ 2 - lo ^ 2) / 2) + β * (hi - lo) := by
  have h1 : IntervalIntegrable (fun x : ℝ => α * x) MeasureTheory.volume lo hi :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun _ : ℝ => β) MeasureTheory.volume lo hi :=
    intervalIntegrable_const
  rw [show (∫ x in lo..hi, (α * x + β)) = (∫ x in lo..hi, α * x) + ∫ _x in lo..hi, β from
    intervalIntegral.integral_add h1 h2]
  rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp [smul_eq_mul]; ring

lemma platT_eq (a δ φ q : ℝ) (hδ : 0 < δ) : platformPayoffT a δ φ q = φ * (a - q) * q := by
  unfold platformPayoffT PlatformFinance.WinWin.uniformMean
  have hf : (fun x : ℝ => φ * (x - q) * q) = fun x => (φ * q) * x + (-(φ * q * q)) := by
    funext x; ring
  rw [hf, int_lin]
  field_simp
  ring

lemma platP_eq (a δ φ rf r w q : ℝ) (hδ : 0 < δ) (hk : 0 < 1 - φ) (hq : 0 ≤ q)
    (hcond : w * (1 + r) ≤ (1 - φ) * (a - δ - q)) :
    platformPayoffP a δ φ rf r w q = φ * (a - q) * q + w * q * (1 + r) - w * q * (1 + rf) := by
  unfold platformPayoffP PlatformFinance.WinWin.uniformMean
  have hcongr : (∫ x in (a - δ)..(a + δ),
      (φ * (x - q) * q + min ((1 - φ) * (x - q) * q) (w * q * (1 + r))))
      = ∫ x in (a - δ)..(a + δ), ((φ * q) * x + (w * q * (1 + r) - φ * q * q)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hx1 : a - δ ≤ x := hx.1
    have hle : w * (1 + r) ≤ (1 - φ) * (x - q) := by nlinarith
    have hle' : w * q * (1 + r) ≤ (1 - φ) * (x - q) * q := by nlinarith [mul_le_mul_of_nonneg_right hle hq]
    simp only
    rw [min_eq_right hle']
    ring
  rw [hcongr, int_lin]
  field_simp
  ring

lemma d2_le_d1 (a δ φ c rf : ℝ) (hk : 0 < 1 - φ) (hδ : 0 < δ)
    (h : δ ≤ delta2 a φ c rf) : δ ≤ PlatformFinance.WinWin.delta1 a φ c rf := by
  have h6 : (2.449 : ℝ) < √6 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h10 : (3.162 : ℝ) < √10 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  unfold delta2 at h
  unfold PlatformFinance.WinWin.delta1 PlatformFinance.WinWin.K0
  have hpos : 0 < (√6 + 2) * (1 - φ) := by positivity
  rw [le_div_iff₀ hpos] at h
  rw [le_div_iff₀ (by positivity)]
  have hK : 0 ≤ (1 - φ) * a - c * (1 + rf) := by nlinarith
  have hcoef : 0 ≤ 5 * √10 - 14 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h hcoef, mul_pos hδ hk]

lemma profP (a δ φ c rf r : ℝ) (hδ : 0 < δ) (hφ1 : φ < 1) (hrf : 0 ≤ rf) (hr : -1 < r)
    (hreg : (√6 + 2) * δ * (1 - φ) ≤ (1 - φ) * a - c * (1 + r))
    (σ : PlatformFinance.WinWin.Profile) (hσ : PlatformFinance.WinWin.IsSPEP a δ φ c rf r σ) :
    platformProfitP a δ φ rf r σ =
      φ * (a - ((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ))) * (((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ)))
      + ((1 - φ) * a + c * (1 + r)) / (2 * (1 + r)) * (((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ))) * (1 + r)
      - ((1 - φ) * a + c * (1 + r)) / (2 * (1 + r)) * (((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ))) * (1 + rf) := by
  have hk : 0 < 1 - φ := by linarith
  have hρ : 0 < 1 + r := by linarith
  have h6 : 2 < √6 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hδk : 0 < δ * (1 - φ) := mul_pos hδ hk
  have hM : (3 + √6) * δ ≤ a + δ - c * (1 + r) / (1 - φ) := by
    have : c * (1 + r) / (1 - φ) ≤ a - (√6 + 2) * δ := by rw [div_le_iff₀ hk]; nlinarith
    linarith
  have hrq : c * (1 + r) < (a + δ) * (1 - φ) := by nlinarith
  obtain ⟨hord, hI, -⟩ := PFW3.charP a δ φ c rf r hδ hφ1 hrf hr hrq σ hσ
  have hb := hI hM
  have hW : σ.w * (1 + r) = ((1 - φ) * a + c * (1 + r)) / 2 := by
    have e1 : σ.w * (1 + r) / (1 - φ) = (a + δ) - (a + δ - c * (1 + r) / (1 - φ) + δ) / 2 := by
      linarith
    have e2 : σ.w * (1 + r) = ((a + δ) - (a + δ - c * (1 + r) / (1 - φ) + δ) / 2) * (1 - φ) := by
      rw [← e1]; field_simp
    rw [e2]; field_simp; ring
  have hw : σ.w = ((1 - φ) * a + c * (1 + r)) / (2 * (1 + r)) := by
    rw [eq_div_iff (by positivity)]; linarith
  have h3 : 3 * δ ≤ a + δ - σ.w * (1 + r) / (1 - φ) := by
    rw [hb]; nlinarith [mul_lt_mul_of_pos_right h6 hδ]
  have hq : σ.order σ.w = ((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ)) := by
    rw [hord, if_pos h3, hb]; field_simp; ring
  have hq0 : 0 ≤ ((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ)) := by
    apply div_nonneg _ (by positivity); nlinarith
  have hcond : σ.w * (1 + r) ≤ (1 - φ) * (a - δ - ((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ))) := by
    rw [hW]
    have : (1 - φ) * (a - δ - ((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ)))
        = (3 * (1 - φ) * a + c * (1 + r)) / 4 - (1 - φ) * δ := by field_simp; ring
    rw [this]; nlinarith
  unfold platformProfitP
  rw [hq, platP_eq a δ φ rf r σ.w _ hδ hk hq0 hcond, hw]

/-- Sign of the profit difference: it is `(r - r_f) E / (16 (1-φ)² (1+r))`. -/
lemma final (a φ c rf r s r6v : ℝ) (hk : 0 < 1 - φ) (hφ0 : 0 ≤ φ) (hc : 0 < c) (ha : 0 < a)
    (hrf : 0 ≤ rf) (hx : 0 < 1 + r)
    (hs : s ^ 2 = 8 * a ^ 2 * (2 - φ) * (1 - φ) ^ 3 + φ ^ 2 * (2 * a * (1 - φ) + c * (1 + rf)) ^ 2)
    (hs0 : 0 ≤ s)
    (hr6 : 2 * c * (2 - φ) * r6v = s - 2 * a * (1 - φ) * φ - c * (4 + rf * φ - φ))
    (hsign : 0 < (r - rf) * (r6v - r)) :
    φ * (a - ((1 - φ) * a - c * (1 + rf)) / (4 * (1 - φ))) * (((1 - φ) * a - c * (1 + rf)) / (4 * (1 - φ)))
    < φ * (a - ((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ))) * (((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ)))
      + ((1 - φ) * a + c * (1 + r)) / (2 * (1 + r)) * (((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ))) * (1 + r)
      - ((1 - φ) * a + c * (1 + r)) / (2 * (1 + r)) * (((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ))) * (1 + rf) := by
  set E := -c ^ 2 * (2 - φ) * (1 + r) ^ 2 - φ * c * (2 * (1 - φ) * a + c * (1 + rf)) * (1 + r)
    + 2 * (1 - φ) ^ 3 * a ^ 2 with hE
  set B := φ * (2 * a * (1 - φ) + c * (1 + rf)) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]; apply mul_nonneg hφ0; nlinarith
  have hD : (φ * (a - ((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ))) * (((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ)))
      + ((1 - φ) * a + c * (1 + r)) / (2 * (1 + r)) * (((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ))) * (1 + r)
      - ((1 - φ) * a + c * (1 + r)) / (2 * (1 + r)) * (((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ))) * (1 + rf))
      - φ * (a - ((1 - φ) * a - c * (1 + rf)) / (4 * (1 - φ))) * (((1 - φ) * a - c * (1 + rf)) / (4 * (1 - φ)))
      = (r - rf) * E / (16 * (1 - φ) ^ 2 * (1 + r)) := by
    rw [hE]; field_simp; ring
  have h4E : 4 * (2 - φ) * E = 2 * c * (2 - φ) * (r6v - r) * (s + B + 2 * (2 - φ) * c * (1 + r)) := by
    rw [hE, hB]
    linear_combination (-1 : ℝ) * hs - (s + φ * (2 * a * (1 - φ) + c * (1 + rf)) + 2 * (2 - φ) * c * (1 + r)) * hr6
  have ht : 0 < 2 - φ := by linarith
  have hpos : 0 < s + B + 2 * (2 - φ) * c * (1 + r) := by positivity
  have hprod : 0 < 4 * (2 - φ) * ((r - rf) * E) := by
    have : 4 * (2 - φ) * ((r - rf) * E)
        = 2 * c * (2 - φ) * (s + B + 2 * (2 - φ) * c * (1 + r)) * ((r - rf) * (r6v - r)) := by
      linear_combination (r - rf) * h4E
    rw [this]; positivity
  have hrE : 0 < (r - rf) * E := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ) ≤ 4 * (2 - φ) by linarith) hh]
  have : 0 < (r - rf) * E / (16 * (1 - φ) ^ 2 * (1 + r)) := by positivity
  linarith

/-- `r₆ - r_f` has the sign of `a(1-φ)² - c(1+r_f)`. -/
lemma r6_sign (a φ c rf s r6v : ℝ) (hk : 0 < 1 - φ) (hφ0 : 0 ≤ φ) (hc : 0 < c) (ha : 0 < a)
    (hrf : 0 ≤ rf)
    (hs : s ^ 2 = 8 * a ^ 2 * (2 - φ) * (1 - φ) ^ 3 + φ ^ 2 * (2 * a * (1 - φ) + c * (1 + rf)) ^ 2)
    (hs0 : 0 ≤ s)
    (hr6 : 2 * c * (2 - φ) * r6v = s - 2 * a * (1 - φ) * φ - c * (4 + rf * φ - φ)) :
    2 * c * (2 - φ) * (r6v - rf) * (s + φ * (2 * a * (1 - φ) + c * (1 + rf)) + 2 * (2 - φ) * c * (1 + rf))
      = 8 * (2 - φ) * (a * (1 - φ) ^ 2 - c * (1 + rf)) * ((1 - φ) * a + c * (1 + rf)) ∧
    0 < s + φ * (2 * a * (1 - φ) + c * (1 + rf)) + 2 * (2 - φ) * c * (1 + rf) := by
  constructor
  · linear_combination hs + (s + φ * (2 * a * (1 - φ) + c * (1 + rf)) + 2 * (2 - φ) * c * (1 + rf)) * hr6
  · have : 0 ≤ φ * (2 * a * (1 - φ) + c * (1 + rf)) := by
      apply mul_nonneg hφ0; nlinarith
    have ht : 0 < 2 - φ := by linarith
    nlinarith [mul_pos (mul_pos ht hc) (show (0:ℝ) < 1 + rf by linarith)]

end PFW7

set_option maxHeartbeats 1000000 in
open PlatformFinance.PlatformProfit in
theorem solution (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (hδ2 : δ ≤ delta2 a φ c rf)
    (σT : PlatformFinance.WinWin.Profile) (hT : PlatformFinance.WinWin.IsSPET a δ φ c rf σT)
    (σP : ℝ → PlatformFinance.WinWin.Profile)
    (hP : ∀ r : ℝ, -1 < r → c * (1 + r) < (a + δ) * (1 - φ) → PlatformFinance.WinWin.IsSPEP a δ φ c rf r (σP r)) :
    (c ≤ cbar a φ rf →
        rf ≤ r6 a φ c rf ∧
          ∀ r : ℝ, rf < r → r < r5 a δ φ c rf →
            platformProfitT a δ φ σT < platformProfitP a δ φ rf r (σP r)) ∧
      (cbar a φ rf < c →
        r6 a φ c rf < rf ∧
          ∀ r : ℝ, -1 < r → r6 a φ c rf < r → r < rf →
            platformProfitT a δ φ σT < platformProfitP a δ φ rf r (σP r)) := by
  have hk : 0 < 1 - φ := by linarith
  have ha : 0 < a := by linarith
  have ht : 0 < 2 - φ := by linarith
  have h6 : 2 < √6 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  -- trade-credit side
  have hd1 := PFW7.d2_le_d1 a δ φ c rf hk hδ hδ2
  obtain ⟨hordT, hI, -⟩ := PFW3.charT a δ φ c rf hδ hφ1 hprof σT hT
  obtain ⟨hbT, hA4⟩ := hI hd1
  have hqT : σT.order σT.w = ((1 - φ) * a - c * (1 + rf)) / (4 * (1 - φ)) := by
    rw [hordT, if_pos (by rw [hbT]; linarith), hbT]; field_simp; ring
  have hPT : platformProfitT a δ φ σT
      = φ * (a - ((1 - φ) * a - c * (1 + rf)) / (4 * (1 - φ)))
          * (((1 - φ) * a - c * (1 + rf)) / (4 * (1 - φ))) := by
    unfold platformProfitT; rw [PFW7.platT_eq _ _ _ _ hδ, hqT]
  -- δ ≤ δ₂ in product form
  have hreg2 : (√6 + 2) * δ * (1 - φ) ≤ (1 - φ) * a - c * (1 + rf) := by
    unfold delta2 at hδ2
    rw [le_div_iff₀ (by positivity)] at hδ2; linarith
  -- r₆ data
  set s := √(8 * a ^ 2 * (2 - φ) * (1 - φ) ^ 3 + φ ^ 2 * (2 * a * (1 - φ) + c * (1 + rf)) ^ 2) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs : s ^ 2 = 8 * a ^ 2 * (2 - φ) * (1 - φ) ^ 3 + φ ^ 2 * (2 * a * (1 - φ) + c * (1 + rf)) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hr6 : 2 * c * (2 - φ) * r6 a φ c rf = s - 2 * a * (1 - φ) * φ - c * (4 + rf * φ - φ) := by
    unfold r6; rw [← hsdef]; field_simp
  obtain ⟨hr6e, hr6p⟩ := PFW7.r6_sign a φ c rf s (r6 a φ c rf) hk hφ0 hc ha hrf hs hs0 hr6
  have hcb : ∀ x, cbar a φ rf = x → (c ≤ x ↔ c * (1 + rf) ≤ a * (1 - φ) ^ 2) := by
    intro x hx; rw [← hx]; unfold cbar; rw [le_div_iff₀ (by linarith)]
  have hcb' : cbar a φ rf < c ↔ a * (1 - φ) ^ 2 < c * (1 + rf) := by
    unfold cbar; rw [div_lt_iff₀ (by linarith)]
  have hka : 0 < (1 - φ) * a + c * (1 + rf) := by nlinarith
  have hcpos : 0 < 2 * c * (2 - φ) := by positivity
  refine ⟨fun hcl => ⟨?_, fun r hr1 hr2 => ?_⟩, fun hcl => ⟨?_, fun r hrm1 hr1 hr2 => ?_⟩⟩
  · have h1 := (hcb _ rfl).1 hcl
    by_contra hh; push Not at hh
    have : 2 * c * (2 - φ) * (r6 a φ c rf - rf) < 0 := by nlinarith
    nlinarith [mul_neg_of_neg_of_pos this hr6p,
      mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 8 * (2 - φ) by linarith) (sub_nonneg.2 h1)) hka.le]
  · have hr1' : r < r1 a δ φ c := lt_of_lt_of_le hr2 (min_le_left _ _)
    have hr6' : r < r6 a φ c rf := lt_of_lt_of_le hr2 (min_le_right _ _)
    have hreg : (√6 + 2) * δ * (1 - φ) ≤ (1 - φ) * a - c * (1 + r) := by
      unfold r1 at hr1'
      have : c * (1 + r) < (1 - φ) * (a - (√6 + 2) * δ) := by
        have h' : r + 1 < (1 - φ) * (a - (√6 + 2) * δ) / c := by linarith
        rw [lt_div_iff₀ hc] at h'; linarith
      nlinarith
    have hr : -1 < r := by linarith
    have hrq : c * (1 + r) < (a + δ) * (1 - φ) := by
      nlinarith [mul_pos hδ hk, mul_pos (mul_pos (by positivity : (0:ℝ) < √6 + 2) hδ) hk]
    rw [hPT, PFW7.profP a δ φ c rf r hδ hφ1 hrf hr hreg (σP r) (hP r hr hrq)]
    exact PFW7.final a φ c rf r s (r6 a φ c rf) hk hφ0 hc ha hrf (by linarith) hs hs0 hr6
      (mul_pos (by linarith) (by linarith))
  · have h1 := hcb'.1 hcl
    by_contra hh; push Not at hh
    have : 0 ≤ 2 * c * (2 - φ) * (r6 a φ c rf - rf) := mul_nonneg hcpos.le (by linarith)
    nlinarith [mul_nonneg this hr6p.le,
      mul_pos (mul_pos (show (0:ℝ) < 8 * (2 - φ) by linarith) (sub_pos.2 h1)) hka]
  · have hreg : (√6 + 2) * δ * (1 - φ) ≤ (1 - φ) * a - c * (1 + r) := by
      have : c * (1 + r) < c * (1 + rf) := by nlinarith
      linarith
    have hrq : c * (1 + r) < (a + δ) * (1 - φ) := by
      nlinarith [mul_pos hδ hk, mul_pos (mul_pos (by positivity : (0:ℝ) < √6 + 2) hδ) hk]
    rw [hPT, PFW7.profP a δ φ c rf r hδ hφ1 hrf hrm1 hreg (σP r) (hP r hrm1 hrq)]
    exact PFW7.final a φ c rf r s (r6 a φ c rf) hk hφ0 hc ha hrf (by linarith) hs hs0 hr6
      (mul_pos_of_neg_of_neg (by linarith) (by linarith))
