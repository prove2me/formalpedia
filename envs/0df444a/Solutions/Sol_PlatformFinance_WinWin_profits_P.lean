-- Prove2me | solution 1 for PlatformFinance.WinWin.profits_P
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T17:38:53.520229+00:00
-- url     : https://prove2.me/submissions/677e8a04-7dce-4657-a7e6-ea6e8420cb29

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model

/-!
Platform-financing equilibrium profits (Huang, Lai, Wang & Xiao, proof of Proposition 2).
The seller owes `w(1+r)` per unit; her payoff in closed form and its unique maximiser (Lemma 1)
give the supplier objective `(w-c)q(w)(1+r_f)` as a function of `b = a + δ - w(1+r)/(1-φ)`;
the least maximiser is unique.
-/

set_option autoImplicit false

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

open PlatformFinance.WinWin in
theorem solution (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hc : 0 < c)
    (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (r : ℝ) (hr : -1 < r) (hrq : c * (1 + r) < (a + δ) * (1 - φ))
    (σ : Profile) (hσ : IsSPEP a δ φ c rf r σ) :
    sellerProfitP a δ φ r σ =
        (if δ ≤ deltaR a φ c r then (a * (1 - φ) - c * (1 + r)) ^ 2 / (16 * (1 - φ))
         else ((a + δ) * (1 - φ) - c * (1 + r)) ^ 3 / (216 * δ * (1 - φ) ^ 2)) ∧
      supplierProfitP c rf σ =
        (if δ ≤ deltaR a φ c r then
          (1 + rf) * (a * (1 - φ) - c * (1 + r)) ^ 2 / (8 * (r + 1) * (1 - φ))
         else (1 + rf) * ((a + δ) * (1 - φ) - c * (1 + r)) ^ 2 / (12 * (1 + r) * (1 - φ))) := by
  have hk : 0 < 1 - φ := by linarith
  have hρ : 0 < 1 + r := by linarith
  have hrf1 : 0 < 1 + rf := by linarith
  have hm : 0 < (1 + rf) * ((1 - φ) / (1 + r)) := by positivity
  have hs : 0 < (1 + r) / (1 - φ) := by positivity
  obtain ⟨hR, hmax, hlt⟩ := hσ
  obtain ⟨M, hMdef⟩ : ∃ M, M = a + δ - c * (1 + r) / (1 - φ) := ⟨_, rfl⟩
  have hkM : (a + δ) * (1 - φ) - c * (1 + r) = (1 - φ) * M := by
    rw [hMdef]; field_simp
  have hkM' : a * (1 - φ) - c * (1 + r) = (1 - φ) * (M - δ) := by
    rw [hMdef]; field_simp; ring
  have hM0 : 0 < M := by
    have : 0 < (1 - φ) * M := by rw [← hkM]; linarith
    nlinarith
  have hPhi : ∀ w, supplierPayoffP c rf w (σ.order w)
      = ((1 + rf) * ((1 - φ) / (1 + r))) * PFWP.psi M δ (a + δ - w * (1 + r) / (1 - φ)) :=
    fun w => PFWP.PhiP_eq a δ φ c rf r w M σ.order hδ hk hρ hR hMdef
  have ht : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have ht2 : 2 < Real.sqrt 6 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have ht3 : Real.sqrt 6 < 3 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hdR : δ ≤ deltaR a φ c r ↔ (3 + Real.sqrt 6) * δ ≤ M := by
    unfold deltaR
    rw [hkM', show (1 - φ) * (M - δ) / ((2 + Real.sqrt 6) * (1 - φ)) = (M - δ) / (2 + Real.sqrt 6) by
      field_simp, le_div_iff₀ (by positivity)]
    constructor <;> intro h <;> linarith
  unfold sellerProfitP supplierProfitP
  by_cases hd : δ ≤ deltaR a φ c r
  · rw [if_pos hd, if_pos hd]
    have hd' := hdR.mp hd
    have htd : 2 * δ < Real.sqrt 6 * δ := mul_lt_mul_of_pos_right ht2 hδ
    have hM5 : 5 * δ ≤ M := by linarith
    obtain ⟨ws, hws⟩ : ∃ ws, ws = (1 - φ) * (a + δ - (M + δ) / 2) / (1 + r) := ⟨_, rfl⟩
    have hbw : ∀ v, a + δ - v * (1 + r) / (1 - φ)
        = (M + δ) / 2 + (ws - v) * ((1 + r) / (1 - φ)) := by
      intro v; rw [hws]; field_simp; ring
    obtain ⟨hw, hval⟩ := PFWP.sup_char2 (fun v => supplierPayoffP c rf v (σ.order v))
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
    rw [if_pos (by linarith)] at hord
    rw [hw, hval, hord, PFWP.seller_cf2 a δ φ _ _ ((M + δ) / 2) hδ hk (by linarith) hbT,
      PFWP.gA0 _ δ (by linarith) hδ, hkM']
    constructor
    · field_simp; ring
    · rw [show r + 1 = 1 + r by ring]; field_simp
  · rw [if_neg hd, if_neg hd]
    have hd' : M < (3 + Real.sqrt 6) * δ := lt_of_not_ge (fun h => hd (hdR.mpr h))
    have htd : Real.sqrt 6 * δ < 3 * δ := mul_lt_mul_of_pos_right ht3 hδ
    have hM6 : M < 6 * δ := by linarith
    obtain ⟨ws, hws⟩ : ∃ ws, ws = (1 - φ) * (a + δ - M / 2) / (1 + r) := ⟨_, rfl⟩
    have hbw : ∀ v, a + δ - v * (1 + r) / (1 - φ)
        = M / 2 + (ws - v) * ((1 + r) / (1 - φ)) := by
      intro v; rw [hws]; field_simp; ring
    obtain ⟨hw, hval⟩ := PFWP.sup_char2 (fun v => supplierPayoffP c rf v (σ.order v))
      (PFWP.psi M δ) ((1 + rf) * ((1 - φ) / (1 + r))) ((1 + r) / (1 - φ)) (M / 2)
      (M ^ 2 / 12) ws σ.w hm hs
      (fun v => by show supplierPayoffP c rf v (σ.order v) = _; rw [hPhi, hbw])
      (fun b => (PFWP.psiII M δ _ b hδ ht (by linarith) ht3 hM0 hd').1)
      (fun b => (PFWP.psiII M δ _ b hδ ht (by linarith) ht3 hM0 hd').2)
      (PFWP.psiII_val M δ hM0 hM6) (hmax _) (hlt _)
    have hbT : a + δ - ws * (1 + r) / (1 - φ) = M / 2 := by
      rw [hbw]; simp
    have hord := (PFWP.order_eqG a δ φ (fun w => w * (1 + r)) ws (M / 2) σ.order hδ hk hR
      hbT).1 (by linarith)
    rw [if_neg (by linarith)] at hord
    rw [hw, hval, hord, PFWP.seller_cf2 a δ φ _ _ (M / 2) hδ hk (by linarith) hbT,
      PFWP.gB0 _ δ (by linarith) (by linarith), hkM]
    constructor
    · field_simp; ring
    · field_simp
