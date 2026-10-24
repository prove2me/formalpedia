-- Prove2me | solution 1 for StrictCompatLB.MeanField.theorem_4_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T15:34:01.124177+00:00
-- url     : https://prove2.me/submissions/c29e5082-e820-46e7-a540-964f063957ee

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Policy

open Filter Topology Finset
open scoped ENNReal

namespace StrictCompatLB.MeanField.T411

open StrictCompatLB.MeanField PowerTwoChoices.Limit

/-! ### The fixed point -/

section fp
variable (lam : ℝ) (d : ℕ)

lemma fp_zero : fixedPoint lam d 0 = 1 := by simp [fixedPoint]

lemma fp_succ (i : ℕ) : fixedPoint lam d (i + 1) = lam * fixedPoint lam d i ^ d := by
  unfold fixedPoint
  have hS : ∑ k ∈ range (i + 1), d ^ k = (∑ k ∈ range i, d ^ k) * d + 1 := by
    rw [Finset.sum_range_succ', Finset.sum_mul]; simp [pow_succ]
  rw [hS, pow_succ, pow_mul]; ring

variable {lam}

lemma fp_pos (h0 : 0 < lam) (i : ℕ) : 0 < fixedPoint lam d i := pow_pos h0 _

lemma fp_le_pow (h0 : 0 < lam) (h1 : lam < 1) (hd : 1 ≤ d) (i : ℕ) :
    fixedPoint lam d i ≤ lam ^ i := by
  unfold fixedPoint
  apply pow_le_pow_of_le_one h0.le h1.le
  calc i = ∑ k ∈ range i, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun k _ => Nat.one_le_pow _ _ (by omega))

lemma fp_le_one (h0 : 0 < lam) (h1 : lam < 1) (hd : 1 ≤ d) (i : ℕ) : fixedPoint lam d i ≤ 1 :=
  le_trans (fp_le_pow d h0 h1 hd i) (pow_le_one₀ h0.le h1.le)

lemma fp_anti (h0 : 0 < lam) (h1 : lam < 1) (hd : 1 ≤ d) : Antitone (fixedPoint lam d) := by
  apply antitone_nat_of_succ_le
  intro i
  rw [fp_succ]
  have hp := fp_pos d h0 i
  have hp1 := fp_le_one d h0 h1 hd i
  have : fixedPoint lam d i ^ d ≤ fixedPoint lam d i := by
    calc _ ≤ fixedPoint lam d i ^ 1 := pow_le_pow_of_le_one hp.le hp1 hd
      _ = _ := pow_one _
  nlinarith

/-- `π` is a fixed point of (3.3). -/
lemma fp_identity (i : ℕ) (hi : 1 ≤ i) :
    lam * (fixedPoint lam d (i - 1) ^ d - fixedPoint lam d i ^ d) =
      fixedPoint lam d i - fixedPoint lam d (i + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel, fp_succ lam d (j + 1), fp_succ lam d j]
  ring

end fp

/-! ### The factorisation `x^d - y^d = h(x, y) (x - y)` -/

def hpoly (d : ℕ) (x y : ℝ) : ℝ := ∑ k ∈ range d, x ^ k * y ^ (d - 1 - k)

lemma hpoly_mul (d : ℕ) (x y : ℝ) : x ^ d - y ^ d = hpoly d x y * (x - y) := by
  unfold hpoly; rw [geom_sum₂_mul]

lemma hpoly_nonneg (d : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ hpoly d x y :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (pow_nonneg hx _) (pow_nonneg hy _))

lemma hpoly_le_d (d : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    hpoly d x y ≤ d := by
  unfold hpoly
  calc _ ≤ ∑ k ∈ range d, (1 : ℝ) := Finset.sum_le_sum (fun k _ =>
        mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy _) (pow_le_one₀ hy hy1))
    _ = d := by simp

lemma geom_tail_le (y : ℝ) (hy : 0 ≤ y) (hy2 : y ≤ 1 / 2) (m : ℕ) :
    ∑ j ∈ range m, y ^ (j + 1) ≤ 2 * y := by
  induction m with
  | zero => simp; linarith
  | succ m ih =>
    rw [Finset.sum_range_succ']
    have : ∑ j ∈ range m, y ^ (j + 1 + 1) = y * ∑ j ∈ range m, y ^ (j + 1) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [this, zero_add, pow_one]
    nlinarith

lemma hpoly_le_small (d : ℕ) (hd : 1 ≤ d) {x y : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (hy2 : y ≤ 1 / 2) : hpoly d x y ≤ 1 + 2 * y := by
  unfold hpoly
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  rw [Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
  have h1 : x ^ m ≤ 1 := pow_le_one₀ hx hx1
  have h2 : ∑ k ∈ range m, x ^ k * y ^ (m - k) ≤ ∑ k ∈ range m, y ^ (m - k) :=
    Finset.sum_le_sum (fun k _ => by
      calc x ^ k * y ^ (m - k) ≤ 1 * y ^ (m - k) :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hx hx1) (pow_nonneg hy _)
        _ = _ := one_mul _)
  have h3 : ∑ k ∈ range m, y ^ (m - k) = ∑ j ∈ range m, y ^ (j + 1) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl; intro j hj
    simp only [mem_range] at hj
    congr 1; omega
  have h4 := geom_tail_le y hy hy2 m
  have : ∑ k ∈ range m, x ^ k * y ^ (m + 1 - 1 - k) = ∑ k ∈ range m, x ^ k * y ^ (m - k) := by
    apply Finset.sum_congr rfl; intro k _; congr 2
  simp only [Nat.add_sub_cancel] at *
  linarith

/-! ### The index `i₀` -/

lemma i0_spec {lam : ℝ} (d : ℕ) (h0 : 0 < lam) (h1 : lam < 1) (hd : 1 ≤ d) :
    1 ≤ i0Index lam d ∧
      lam * (2 * fixedPoint lam d (i0Index lam d) + 1) < (1 + lam) / 2 := by
  have hne : {i : ℕ | 1 ≤ i ∧ lam * (2 * fixedPoint lam d i + 1) < (1 + lam) / 2}.Nonempty := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < (1 - lam) / (4 * lam) by
      apply div_pos <;> linarith) h1
    refine ⟨n + 1, by omega, ?_⟩
    have h2 : fixedPoint lam d (n + 1) < (1 - lam) / (4 * lam) :=
      lt_of_le_of_lt (le_trans (fp_le_pow d h0 h1 hd _) (pow_le_pow_of_le_one h0.le h1.le
        (by omega))) hn
    have h3 : lam * (2 * fixedPoint lam d (n + 1) + 1) < lam * (2 * ((1 - lam) / (4 * lam)) + 1) := by
      apply mul_lt_mul_of_pos_left _ h0; linarith
    have h4 : lam * (2 * ((1 - lam) / (4 * lam)) + 1) = (1 + lam) / 2 := by
      field_simp; ring
    linarith
  exact Nat.sInf_mem hne

lemma fp_i0_le_half {lam : ℝ} (d : ℕ) (h0 : 0 < lam) (h1 : lam < 1) (hd : 1 ≤ d) :
    fixedPoint lam d (i0Index lam d) ≤ 1 / 2 := by
  obtain ⟨hI, hc⟩ := i0_spec d h0 h1 hd
  have hp := fp_pos d h0 (i0Index lam d)
  have hle : fixedPoint lam d (i0Index lam d) ≤ lam :=
    le_trans (fp_le_pow d h0 h1 hd _) (by
      calc lam ^ i0Index lam d ≤ lam ^ 1 := pow_le_pow_of_le_one h0.le h1.le hI
        _ = lam := pow_one _)
  by_cases hl : lam ≤ 1 / 2
  · linarith
  · push Not at hl
    nlinarith

/-! ### The weights -/

/-- `w_i = ∑_{j<i} q^j` for `1 ≤ i ≤ I`, `w_i = w_I r^{i - I}` for `i ≥ I`, `w_0 = 0`. -/
noncomputable def wt (I : ℕ) (q r : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else if i ≤ I then ∑ j ∈ range i, q ^ j else (∑ j ∈ range I, q ^ j) * r ^ (i - I)

lemma wt_zero (I : ℕ) (q r : ℝ) : wt I q r 0 = 0 := by simp [wt]

section weights
variable (I : ℕ) (q r : ℝ) (hI : 1 ≤ I) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (hr : 1 ≤ r)
include hI hq0 hq hr

lemma geom_le_two (i : ℕ) : ∑ j ∈ range i, q ^ j ≤ 2 := by
  have h := geom_sum_eq (show q ≠ 1 by linarith) i
  rw [h]
  have : 0 < 1 - q := by linarith
  rw [div_le_iff_of_neg (by linarith)]
  have : 0 ≤ q ^ i := pow_nonneg hq0.le _
  nlinarith

lemma geom_ge_one (i : ℕ) (hi : 1 ≤ i) : 1 ≤ ∑ j ∈ range i, q ^ j := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [pow_zero]
  have : 0 ≤ ∑ j ∈ range k, q ^ (j + 1) := Finset.sum_nonneg (fun j _ => pow_nonneg hq0.le _)
  linarith

lemma wt_low (i : ℕ) (hi : 1 ≤ i) (hiI : i ≤ I) : wt I q r i = ∑ j ∈ range i, q ^ j := by
  simp [wt, show i ≠ 0 by omega, hiI]

lemma wt_high (i : ℕ) (hi : I ≤ i) : wt I q r i = wt I q r I * r ^ (i - I) := by
  rw [wt_low I q r hI hq0 hq hr I hI le_rfl]
  rcases eq_or_lt_of_le hi with h | h
  · subst h; simp [wt, show I ≠ 0 by omega]
  · simp [wt, show i ≠ 0 by omega, show ¬ i ≤ I by omega]

lemma wt_ge_one (i : ℕ) (hi : 1 ≤ i) : 1 ≤ wt I q r i := by
  by_cases hiI : i ≤ I
  · rw [wt_low I q r hI hq0 hq hr i hi hiI]; exact geom_ge_one I q r hI hq0 hq hr i hi
  · push Not at hiI
    rw [wt_high I q r hI hq0 hq hr i hiI.le, wt_low I q r hI hq0 hq hr I hI le_rfl]
    have h1 := geom_ge_one I q r hI hq0 hq hr I hI
    have h2 : 1 ≤ r ^ (i - I) := one_le_pow₀ hr
    nlinarith

lemma wt_I_le_two : wt I q r I ≤ 2 := by
  rw [wt_low I q r hI hq0 hq hr I hI le_rfl]; exact geom_le_two I q r hI hq0 hq hr I

lemma wt_low_le_two (i : ℕ) (hiI : i ≤ I) : wt I q r i ≤ 2 := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; rw [wt_zero]; norm_num
  · rw [wt_low I q r hI hq0 hq hr i h hiI]; exact geom_le_two I q r hI hq0 hq hr i

lemma wt_diff_low (i : ℕ) (hi : 1 ≤ i) (hiI : i ≤ I) :
    wt I q r i - wt I q r (i - 1) = q ^ (i - 1) := by
  rw [wt_low I q r hI hq0 hq hr i hi hiI]
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel, Finset.sum_range_succ]
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp [wt_zero]
  · rw [wt_low I q r hI hq0 hq hr k h (by omega)]; ring

/-- The key coefficient inequality. -/
lemma coeff_ineq (lam θ δ : ℝ) (d : ℕ) (hlam : 0 < lam) (hdq : lam * d * q ≤ 1 / 2)
    (hr1 : 1 < r) (hrA : 2 * lam * d * (r - 1) ≤ q ^ (I - 1) / 2) (hrθ : r * θ < 1)
    (hδ1 : δ ≤ q ^ (I - 1) / 4) (hδ2 : δ ≤ (r - 1) * (1 - r * θ) / r)
    (i : ℕ) (hi : 1 ≤ i) (h : ℝ) (hh0 : 0 ≤ h) (hhd : h ≤ d) (hhθ : I < i → lam * h ≤ θ) :
    lam * h * (wt I q r (i + 1) - wt I q r i) - (wt I q r i - wt I q r (i - 1)) ≤
      -δ * wt I q r i := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  rcases lt_trichotomy i I with hlt | heq | hgt
  · have e1 := wt_diff_low I q r hI hq0 hq hr (i + 1) (by omega) (by omega)
    have e2 := wt_diff_low I q r hI hq0 hq hr i hi hlt.le
    rw [Nat.add_sub_cancel] at e1
    rw [e1, e2]
    have hqi : q ^ i = q * q ^ (i - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h1 : lam * h * q ^ i ≤ q ^ (i - 1) / 2 := by
      rw [hqi]
      have : lam * h * q ≤ 1 / 2 := by
        calc lam * h * q ≤ lam * d * q := by
              apply mul_le_mul_of_nonneg_right _ hq0.le
              exact mul_le_mul_of_nonneg_left hhd hlam.le
          _ ≤ _ := hdq
      have hp : 0 ≤ q ^ (i - 1) := pow_nonneg hq0.le _
      nlinarith
    have h2 : q ^ (I - 1) ≤ q ^ (i - 1) := pow_le_pow_of_le_one hq0.le (by linarith) (by omega)
    have h3 : wt I q r i ≤ 2 := wt_low_le_two I q r hI hq0 hq hr i hlt.le
    have h4 : 0 ≤ δ * wt I q r i ∨ δ * wt I q r i < 0 := le_or_gt _ _
    have h5 : δ * wt I q r i ≤ q ^ (I - 1) / 2 := by
      rcases le_or_gt 0 δ with hδ0 | hδ0
      · calc δ * wt I q r i ≤ δ * 2 := mul_le_mul_of_nonneg_left h3 hδ0
          _ ≤ q ^ (I - 1) / 4 * 2 := by linarith
          _ = _ := by ring
      · have : 0 < wt I q r i := lt_of_lt_of_le one_pos (wt_ge_one I q r hI hq0 hq hr i hi)
        have : δ * wt I q r i < 0 := mul_neg_of_neg_of_pos hδ0 this
        have : 0 ≤ q ^ (I - 1) := pow_nonneg hq0.le _
        linarith
    linarith
  · subst heq
    have e1 : wt i q r (i + 1) - wt i q r i = wt i q r i * (r - 1) := by
      rw [wt_high i q r hI hq0 hq hr (i + 1) (by omega)]
      rw [show i + 1 - i = 1 by omega, pow_one]; ring
    have e2 := wt_diff_low i q r hI hq0 hq hr i hi le_rfl
    rw [e1, e2]
    have hw2 := wt_I_le_two i q r hI hq0 hq hr
    have hw1 := wt_ge_one i q r hI hq0 hq hr i hi
    have h1 : lam * h * (wt i q r i * (r - 1)) ≤ 2 * lam * d * (r - 1) := by
      have hlh : lam * h ≤ lam * d := mul_le_mul_of_nonneg_left hhd hlam.le
      have hr0 : 0 ≤ r - 1 := by linarith
      calc lam * h * (wt i q r i * (r - 1)) ≤ lam * d * (2 * (r - 1)) := by
            apply mul_le_mul hlh (mul_le_mul_of_nonneg_right hw2 hr0)
              (mul_nonneg (by linarith) hr0) (by positivity)
        _ = _ := by ring
    have h5 : δ * wt i q r i ≤ q ^ (i - 1) / 2 := by
      rcases le_or_gt 0 δ with hδ0 | hδ0
      · calc δ * wt i q r i ≤ δ * 2 := mul_le_mul_of_nonneg_left hw2 hδ0
          _ ≤ q ^ (i - 1) / 4 * 2 := by linarith
          _ = _ := by ring
      · have : δ * wt i q r i < 0 := mul_neg_of_neg_of_pos hδ0 (by linarith)
        have : 0 ≤ q ^ (i - 1) := pow_nonneg hq0.le _
        linarith
    linarith
  · have hθ := hhθ hgt
    have e1 : wt I q r (i + 1) - wt I q r i = wt I q r i * (r - 1) := by
      rw [wt_high I q r hI hq0 hq hr (i + 1) (by omega), wt_high I q r hI hq0 hq hr i (by omega)]
      rw [show i + 1 - I = (i - I) + 1 by omega, pow_succ]; ring
    have e2 : wt I q r i - wt I q r (i - 1) = wt I q r i * (r - 1) / r := by
      rw [wt_high I q r hI hq0 hq hr i (by omega), wt_high I q r hI hq0 hq hr (i - 1) (by omega)]
      have : i - I = (i - 1 - I) + 1 := by omega
      rw [this, pow_succ]
      field_simp
    rw [e1, e2]
    have hw := lt_of_lt_of_le one_pos (wt_ge_one I q r hI hq0 hq hr i hi)
    have hr0 : 0 < r := by linarith
    have key : lam * h * (wt I q r i * (r - 1)) - wt I q r i * (r - 1) / r =
        wt I q r i * (r - 1) * (lam * h - 1 / r) := by field_simp
    rw [key]
    have h1 : lam * h - 1 / r ≤ θ - 1 / r := by linarith
    have h2 : θ - 1 / r = -((1 - r * θ) / r) := by field_simp; ring
    have h3 : 0 ≤ wt I q r i * (r - 1) := mul_nonneg hw.le (by linarith)
    calc wt I q r i * (r - 1) * (lam * h - 1 / r) ≤ wt I q r i * (r - 1) * (θ - 1 / r) :=
          mul_le_mul_of_nonneg_left h1 h3
      _ = -(wt I q r i * ((r - 1) * (1 - r * θ) / r)) := by rw [h2]; ring
      _ ≤ -(wt I q r i * δ) := by
          apply neg_le_neg
          exact mul_le_mul_of_nonneg_left hδ2 hw.le
      _ = _ := by ring

end weights

/-! ### Right derivative of `|f|` -/

/-- The right derivative of `|f|` at a point where `f(t) = a` and `f'(t) = F`. -/
noncomputable def absD (a F : ℝ) : ℝ := if a = 0 then |F| else if 0 < a then F else -F

lemma abs_hasDerivWithinAt (f : ℝ → ℝ) (F t : ℝ) (hf : HasDerivWithinAt f F (Set.Ici t) t) :
    HasDerivWithinAt (fun u => |f u|) (absD (f t) F) (Set.Ici t) t := by
  by_cases h0 : f t = 0
  · simp only [absD, if_pos h0]
    rw [hasDerivWithinAt_iff_isLittleO] at hf ⊢
    refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound 1 ?_) hf
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [Set.mem_Ici] at hu
    simp only [h0, abs_zero, sub_zero, smul_eq_mul, Real.norm_eq_abs, one_mul]
    have : (u - t) * |F| = |(u - t) * F| := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ u - t by linarith)]
    rw [this]
    exact abs_abs_sub_abs_le_abs_sub _ _
  · by_cases hp : 0 < f t
    · simp only [absD, if_neg h0, if_pos hp]
      apply hf.congr_of_eventuallyEq _ (abs_of_pos hp)
      have := hf.continuousWithinAt.eventually (eventually_gt_nhds hp)
      filter_upwards [this] with u hu
      exact abs_of_pos hu
    · have hn : f t < 0 := lt_of_le_of_ne (not_lt.mp hp) h0
      simp only [absD, if_neg h0, if_neg hp]
      apply hf.neg.congr_of_eventuallyEq _ (abs_of_neg hn)
      have := hf.continuousWithinAt.eventually (eventually_lt_nhds hn)
      filter_upwards [this] with u hu
      exact abs_of_neg hu

lemma absD_le (a F p q x y : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hF : F = p * x - (q + 1) * a + y) :
    absD a F ≤ p * |x| - (q + 1) * |a| + |y| := by
  unfold absD
  have hpx : p * x ≤ p * |x| := mul_le_mul_of_nonneg_left (le_abs_self x) hp
  have hpx' : -(p * x) ≤ p * |x| := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le x) hp; linarith
  split_ifs with h0 h1
  · rw [hF, h0]; simp only [mul_zero, sub_zero, abs_zero, add_zero]
    calc |p * x + y| ≤ |p * x| + |y| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg hp]
  · rw [abs_of_pos h1, hF]; linarith [le_abs_self y]
  · have hn : a < 0 := lt_of_le_of_ne (not_lt.mp h1) h0
    rw [abs_of_neg hn, hF]; linarith [neg_abs_le y]

/-- The algebraic core of the differential inequality for the truncated potential. -/
lemma telescope (w e hh : ℕ → ℝ) (lam δ : ℝ) (hw0 : w 0 = 0) (he0 : e 0 = 0) (hlam : 0 ≤ lam)
    (hh0 : ∀ i, 0 ≤ hh i)
    (coef : ∀ i, 1 ≤ i → lam * hh i * (w (i + 1) - w i) - (w i - w (i - 1)) ≤ -δ * w i)
    (n : ℕ) :
    ∑ i ∈ range n, w (i + 1) * (lam * hh i * |e i| - (lam * hh (i + 1) + 1) * |e (i + 1)| +
        |e (i + 2)|) ≤
      -δ * ∑ i ∈ range n, w (i + 1) * |e (i + 1)| + w n * |e (n + 1)| -
        w (n + 1) * (lam * hh n) * |e n| := by
  induction n with
  | zero => simp [hw0, he0]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hc := coef (n + 1) (by omega)
    rw [Nat.add_sub_cancel] at hc
    have ha : 0 ≤ |e (n + 1)| := abs_nonneg _
    have key : (w n - w (n + 1) * (lam * hh (n + 1) + 1) + δ * w (n + 1) +
        w (n + 2) * (lam * hh (n + 1))) * |e (n + 1)| ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ ha
      nlinarith
    nlinarith

/-! ### Grönwall in the form used below -/

lemma gron {f D : ℝ → ℝ} {T K ε δ0 : ℝ} (hf : ContinuousOn f (Set.Icc 0 T))
    (hD : ∀ x ∈ Set.Ico 0 T, HasDerivWithinAt f (D x) (Set.Ici x) x) (h0 : f 0 ≤ δ0)
    (hb : ∀ x ∈ Set.Ico 0 T, D x ≤ K * f x + ε) :
    ∀ x ∈ Set.Icc 0 T, f x ≤ gronwallBound δ0 K ε x := by
  have := le_gronwallBound_of_liminf_deriv_right_le hf
    (fun x hx r hr => by
      have := (hD x hx).liminf_right_slope_le hr
      refine this.mono (fun z hz => ?_)
      rw [slope_def_field] at hz
      rwa [div_eq_inv_mul] at hz) h0 hb
  intro x hx
  simpa using this x hx

/-! ### Trajectories -/

section traj
variable {lam : ℝ} {d : ℕ} {s : ℝ → ℕ → ℝ}

lemma st_nonneg (hs : IsTrajectory lam d s) {t : ℝ} (ht : 0 ≤ t) (i : ℕ) : 0 ≤ s t i :=
  (hs.1 t ht).2.1 i

lemma st_le_one (hs : IsTrajectory lam d s) {t : ℝ} (ht : 0 ≤ t) (i : ℕ) : s t i ≤ 1 := by
  have h := (hs.1 t ht).2.2 (Nat.zero_le i)
  rw [(hs.1 t ht).1] at h; exact h

lemma st_anti (hs : IsTrajectory lam d s) {t : ℝ} (ht : 0 ≤ t) {i j : ℕ} (hij : i ≤ j) :
    s t j ≤ s t i := (hs.1 t ht).2.2 hij

lemma st_zero (hs : IsTrajectory lam d s) {t : ℝ} (ht : 0 ≤ t) : s t 0 = 1 := (hs.1 t ht).1

lemma st_deriv (hs : IsTrajectory lam d s) {i : ℕ} (hi : 1 ≤ i) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u => s u i) (drift lam d (s t) i) (Set.Ici t) t :=
  (hs.2 i hi t ht).mono (Set.Ici_subset_Ici.mpr ht)

lemma st_cont (hs : IsTrajectory lam d s) {i : ℕ} (hi : 1 ≤ i) (T : ℝ) :
    ContinuousOn (fun u => s u i) (Set.Icc 0 T) := by
  intro u hu
  exact ((hs.2 i hi u hu.1).continuousWithinAt).mono (fun x hx => hx.1)

lemma drift_decomp (hd : 1 ≤ d) (hs : IsTrajectory lam d s) {i : ℕ} (hi : 1 ≤ i) (t : ℝ) :
    drift lam d (s t) i =
      lam * hpoly d (s t (i - 1)) (fixedPoint lam d (i - 1)) *
          (s t (i - 1) - fixedPoint lam d (i - 1)) -
        (lam * hpoly d (s t i) (fixedPoint lam d i) + 1) * (s t i - fixedPoint lam d i) +
        (s t (i + 1) - fixedPoint lam d (i + 1)) := by
  have e1 := hpoly_mul d (s t (i - 1)) (fixedPoint lam d (i - 1))
  have e2 := hpoly_mul d (s t i) (fixedPoint lam d i)
  have e3 := fp_identity (lam := lam) d i hi
  unfold drift
  linear_combination lam * e1 - lam * e2 + e3

/-- The deviation `ε_i(t) = s_i(t) − π_i`. -/
def eps (lam : ℝ) (d : ℕ) (s : ℝ → ℕ → ℝ) (i : ℕ) (t : ℝ) : ℝ := s t i - fixedPoint lam d i

/-- The truncated potential `Φ_n(t) = ∑_{i=1}^n w_i |ε_i(t)|`. -/
noncomputable def Phi (lam : ℝ) (d : ℕ) (s : ℝ → ℕ → ℝ) (w : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ range n, w (i + 1) * |eps lam d s (i + 1) t|

noncomputable def DPhi (lam : ℝ) (d : ℕ) (s : ℝ → ℕ → ℝ) (w : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ range n, w (i + 1) * absD (eps lam d s (i + 1) t) (drift lam d (s t) (i + 1))

lemma Phi_hasDeriv (hs : IsTrajectory lam d s) (w : ℕ → ℝ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (Phi lam d s w n) (DPhi lam d s w n t) (Set.Ici t) t := by
  unfold Phi DPhi
  apply HasDerivWithinAt.fun_sum
  intro i _
  apply HasDerivWithinAt.const_mul
  have h := (st_deriv hs (show 1 ≤ i + 1 by omega) ht).sub_const (fixedPoint lam d (i + 1))
  exact abs_hasDerivWithinAt (fun u => eps lam d s (i + 1) u) _ t h

lemma Phi_cont (hs : IsTrajectory lam d s) (w : ℕ → ℝ) (n : ℕ) (T : ℝ) :
    ContinuousOn (Phi lam d s w n) (Set.Icc 0 T) := by
  unfold Phi
  apply continuousOn_finsetSum
  intro i _
  apply ContinuousOn.mul continuousOn_const
  exact ((st_cont hs (show 1 ≤ i + 1 by omega) T).sub continuousOn_const).abs

lemma Phi_nonneg (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (n : ℕ) (t : ℝ) : 0 ≤ Phi lam d s w n t :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw _) (abs_nonneg _))

/-- The differential inequality for the truncated potential. -/
lemma DPhi_le (hlam0 : 0 < lam) (hlam1 : lam < 1) (hd : 1 ≤ d) (hs : IsTrajectory lam d s)
    (w : ℕ → ℝ) (δ : ℝ) (hw0 : w 0 = 0) (hw : ∀ i, 0 ≤ w i)
    (coef : ∀ t, 0 ≤ t → ∀ i, 1 ≤ i →
      lam * hpoly d (s t i) (fixedPoint lam d i) * (w (i + 1) - w i) - (w i - w (i - 1)) ≤
        -δ * w i)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    DPhi lam d s w n t ≤ -δ * Phi lam d s w n t + w n * |eps lam d s (n + 1) t| := by
  set hh : ℕ → ℝ := fun j => hpoly d (s t j) (fixedPoint lam d j) with hhh
  set e : ℕ → ℝ := fun j => eps lam d s j t with he
  have hh0 : ∀ j, 0 ≤ hh j := fun j =>
    hpoly_nonneg d (st_nonneg hs ht j) (fp_pos d hlam0 j).le
  have he0 : e 0 = 0 := by simp [he, eps, st_zero hs ht, fp_zero]
  have hterm : ∀ i ∈ range n, w (i + 1) * absD (eps lam d s (i + 1) t) (drift lam d (s t) (i + 1)) ≤
      w (i + 1) * (lam * hh i * |e i| - (lam * hh (i + 1) + 1) * |e (i + 1)| + |e (i + 2)|) := by
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hw _)
    apply absD_le _ _ _ _ _ _ (mul_nonneg hlam0.le (hh0 i)) (mul_nonneg hlam0.le (hh0 (i + 1)))
    rw [drift_decomp hd hs (show 1 ≤ i + 1 by omega) t, Nat.add_sub_cancel]
    simp only [hhh, he, eps]
  have htel := telescope w e hh lam δ hw0 he0 hlam0.le hh0 (fun i hi => coef t ht i hi) n
  have hlast : 0 ≤ w (n + 1) * (lam * hh n) * |e n| :=
    mul_nonneg (mul_nonneg (hw _) (mul_nonneg hlam0.le (hh0 n))) (abs_nonneg _)
  unfold DPhi
  calc _ ≤ _ := Finset.sum_le_sum hterm
    _ ≤ _ := htel
    _ ≤ _ := by
        unfold Phi
        simp only [he] at hlast ⊢
        linarith

end traj

/-! ### A priori bounds -/

section apriori
variable {lam : ℝ} {d : ℕ} {s : ℝ → ℕ → ℝ}

lemma drift_le (hd : 1 ≤ d) (hs : IsTrajectory lam d s) (hlam0 : 0 < lam) {i : ℕ} (hi : 1 ≤ i)
    {t : ℝ} (ht : 0 ≤ t) : drift lam d (s t) i ≤ lam * s t (i - 1) ^ d := by
  unfold drift
  have h1 : 0 ≤ s t i ^ d := pow_nonneg (st_nonneg hs ht i) _
  have h2 : s t (i + 1) ≤ s t i := st_anti hs ht (by omega)
  nlinarith

lemma pow_le_self' {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) {d : ℕ} (hd : 1 ≤ d) : x ^ d ≤ x := by
  calc x ^ d ≤ x ^ 1 := pow_le_pow_of_le_one hx hx1 hd
    _ = x := pow_one x

lemma pow_le_sq' {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) {d : ℕ} (hd : 2 ≤ d) : x ^ d ≤ x ^ 2 :=
  pow_le_pow_of_le_one hx hx1 hd

/-- `U_m(t) = ∑_{i=1}^m r^i s_i(t)`. -/
noncomputable def Usum (s : ℝ → ℕ → ℝ) (r : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ range m, r ^ (i + 1) * s t (i + 1)

/-- `V_{n,m}(t) = ∑_{i<m} r^{n+i} s_{n+i}(t)`. -/
noncomputable def Vsum (s : ℝ → ℕ → ℝ) (r : ℝ) (n m : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ range m, r ^ (n + i) * s t (n + i)

lemma gron_explicit {K ε B T x δ0 : ℝ} (hK : 0 < K) (hε : 0 ≤ ε) (hB : 0 ≤ B) (hδ0 : δ0 ≤ B)
    (hx : 0 ≤ x)
    (hxT : x ≤ T) :
    gronwallBound δ0 K ε x ≤ B * Real.exp (K * T) + ε / K * (Real.exp (K * T) - 1) := by
  rw [gronwallBound_of_K_ne_0 hK.ne']
  simp only
  have e1 : Real.exp (K * x) ≤ Real.exp (K * T) := Real.exp_le_exp.mpr (by nlinarith)
  have e0 : 1 ≤ Real.exp (K * x) := Real.one_le_exp (by nlinarith)
  have hεK : 0 ≤ ε / K := div_nonneg hε hK.le
  have : δ0 * Real.exp (K * x) ≤ B * Real.exp (K * T) := by
    rcases le_or_gt 0 δ0 with h | h
    · calc δ0 * Real.exp (K * x) ≤ B * Real.exp (K * x) :=
            mul_le_mul_of_nonneg_right hδ0 (Real.exp_pos _).le
        _ ≤ B * Real.exp (K * T) := mul_le_mul_of_nonneg_left e1 (le_trans h hδ0)
    · have : δ0 * Real.exp (K * x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h.le (Real.exp_pos _).le
      have := mul_nonneg hB (Real.exp_pos (K * T)).le; linarith
  have : ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (Real.exp (K * T) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hεK
  linarith

/-- Uniform bound on `r^j s_j(t)` on bounded time intervals. -/
lemma U_bound (hd : 1 ≤ d) (hs : IsTrajectory lam d s) (hlam0 : 0 < lam) (r : ℝ) (hr : 1 ≤ r)
    (B0 : ℝ) (hB00 : 0 ≤ B0) (hB0 : ∀ m, Usum s r m 0 ≤ B0) (T : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ t ∈ Set.Icc 0 T, ∀ j, 1 ≤ j → r ^ j * s t j ≤ K := by
  set Kc := lam * r with hKc
  have hKc0 : 0 < Kc := by positivity
  refine ⟨max (B0 * Real.exp (Kc * T) + Kc / Kc * (Real.exp (Kc * T) - 1)) 0, le_max_right _ _, ?_⟩
  intro t ht j hj
  have hUm : ∀ m, Usum s r m t ≤ B0 * Real.exp (Kc * T) + Kc / Kc * (Real.exp (Kc * T) - 1) := by
    intro m
    have hg := gron (f := Usum s r m) (D := fun x => ∑ i ∈ range m, r ^ (i + 1) * drift lam d (s x) (i + 1))
      (T := T) (K := Kc) (ε := Kc) (δ0 := Usum s r m 0)
      (by
        unfold Usum
        apply continuousOn_finsetSum; intro i _
        exact continuousOn_const.mul (st_cont hs (show 1 ≤ i + 1 by omega) T))
      (by
        intro x hx
        unfold Usum
        apply HasDerivWithinAt.fun_sum; intro i _
        exact (st_deriv hs (show 1 ≤ i + 1 by omega) hx.1).const_mul _)
      le_rfl
      (by
        intro x hx
        have hx0 : 0 ≤ x := hx.1
        calc ∑ i ∈ range m, r ^ (i + 1) * drift lam d (s x) (i + 1)
            ≤ ∑ i ∈ range m, r ^ (i + 1) * (lam * s x i) := by
              apply Finset.sum_le_sum; intro i _
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have := drift_le hd hs hlam0 (show 1 ≤ i + 1 by omega) hx0
              rw [Nat.add_sub_cancel] at this
              have := pow_le_self' (st_nonneg hs hx0 i) (st_le_one hs hx0 i) hd
              nlinarith
          _ = Kc * ∑ i ∈ range m, r ^ i * s x i := by
              rw [hKc, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
          _ ≤ Kc * Usum s r m x + Kc := by
              have : ∑ i ∈ range m, r ^ i * s x i ≤ Usum s r m x + 1 := by
                rcases Nat.eq_zero_or_pos m with h0 | hpos
                · subst h0; simp [Usum]
                · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
                  rw [Finset.sum_range_succ', pow_zero, st_zero hs hx0, mul_one]
                  have : Usum s r k x ≤ Usum s r (k + 1) x := by
                    unfold Usum; rw [Finset.sum_range_succ]
                    have := mul_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ r) (k + 1))
                      (st_nonneg hs hx0 (k + 1))
                    linarith
                  unfold Usum at this ⊢
                  linarith
              nlinarith)
      t ht
    exact le_trans hg (gron_explicit hKc0 hKc0.le hB00 (hB0 m) ht.1 ht.2)
  have := hUm j
  have hsingle : r ^ j * s t j ≤ Usum s r j t := by
    unfold Usum
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [Finset.sum_range_succ]
    have : 0 ≤ ∑ i ∈ range k, r ^ (i + 1) * s t (i + 1) := Finset.sum_nonneg (fun i _ =>
      mul_nonneg (pow_nonneg (by linarith) _) (st_nonneg hs ht.1 _))
    linarith
  exact le_trans (le_trans hsingle this) (le_max_left _ _)

end apriori

section main
variable {lam : ℝ} {d : ℕ} {s : ℝ → ℕ → ℝ}

lemma tail_bound (hd : 2 ≤ d) (hs : IsTrajectory lam d s) (hlam0 : 0 < lam) (r : ℝ) (hr : 1 ≤ r)
    (K T : ℝ) (hKb : ∀ t ∈ Set.Icc 0 T, ∀ j, 1 ≤ j → r ^ j * s t j ≤ K) (n : ℕ) (hn : 2 ≤ n) :
    ∀ t ∈ Set.Icc 0 T, r ^ n * s t n ≤ r ^ n * s 0 n + lam * K ^ 2 * r ^ 2 / r ^ n * t := by
  have hr0 : 0 < r := by linarith
  have hg := gron (f := fun u => r ^ n * s u n) (D := fun x => r ^ n * drift lam d (s x) n)
    (T := T) (K := 0) (ε := lam * K ^ 2 * r ^ 2 / r ^ n) (δ0 := r ^ n * s 0 n)
    (continuousOn_const.mul (st_cont hs (show 1 ≤ n by omega) T))
    (fun x hx => (st_deriv hs (show 1 ≤ n by omega) hx.1).const_mul _) le_rfl
    (by
      intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hxT : x ∈ Set.Icc 0 T := ⟨hx.1, hx.2.le⟩
      simp only [zero_mul, zero_add]
      have h1 := drift_le (by omega) hs hlam0 (show 1 ≤ n by omega) hx0
      have hsn := st_nonneg hs hx0 (n - 1)
      have h2 := pow_le_sq' hsn (st_le_one hs hx0 (n - 1)) hd
      have h3 : r ^ (n - 1) * s x (n - 1) ≤ K := hKb x hxT (n - 1) (by omega)
      have hrp : 0 < r ^ (n - 1) := pow_pos hr0 _
      have h4 : s x (n - 1) ≤ K / r ^ (n - 1) := by rw [le_div_iff₀ hrp]; linarith
      have h5 : s x (n - 1) ^ 2 ≤ (K / r ^ (n - 1)) ^ 2 := pow_le_pow_left₀ hsn h4 2
      have hrn : r ^ n = r * r ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
      have e : r ^ n * (lam * (K / r ^ (n - 1)) ^ 2) = lam * K ^ 2 * r ^ 2 / r ^ n := by
        rw [hrn]; field_simp
      have hrnpos : 0 < r ^ n := pow_pos hr0 _
      calc r ^ n * drift lam d (s x) n ≤ r ^ n * (lam * s x (n - 1) ^ d) :=
            mul_le_mul_of_nonneg_left h1 hrnpos.le
        _ ≤ r ^ n * (lam * (K / r ^ (n - 1)) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hrnpos.le
            apply mul_le_mul_of_nonneg_left (le_trans h2 h5) hlam0.le
        _ = _ := e)
  intro t ht
  have := hg t ht
  rw [gronwallBound_K0] at this
  simpa using this

lemma geom_partial_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (m : ℕ) :
    ∑ i ∈ range m, x ^ (i + 1) ≤ 1 / (1 - x) := by
  have h1 : ∑ i ∈ range m, x ^ (i + 1) ≤ ∑ i ∈ range m, x ^ i :=
    Finset.sum_le_sum (fun i _ => pow_le_pow_of_le_one hx0 hx1.le (by omega))
  have h2 := geom_sum_eq (show x ≠ 1 by linarith) m
  have h3 : ∑ i ∈ range m, x ^ i ≤ 1 / (1 - x) := by
    have hpos : 0 < 1 - x := by linarith
    rw [h2, show (x ^ m - 1) / (x - 1) = (1 - x ^ m) / (1 - x) by
      rw [← neg_div_neg_eq, neg_sub, neg_sub]]
    apply div_le_div_of_nonneg_right _ hpos.le
    linarith [pow_nonneg hx0 m]
  linarith

lemma main_estimate (hlam0 : 0 < lam) (hlam1 : lam < 1) (hd : 2 ≤ d) (hs : IsTrajectory lam d s)
    (w : ℕ → ℝ) (I : ℕ) (r δ Φ0 : ℝ) (hr1 : 1 < r) (hrl : r * lam < 1) (hδ : 0 < δ)
    (hw0 : w 0 = 0) (hw : ∀ i, 0 ≤ w i) (hrw : ∀ j, 1 ≤ j → r ^ j ≤ r ^ I * w j)
    (hwn : ∀ n, I ≤ n → w n ≤ 2 / r ^ I * r ^ n)
    (coef : ∀ t, 0 ≤ t → ∀ i, 1 ≤ i →
      lam * hpoly d (s t i) (fixedPoint lam d i) * (w (i + 1) - w i) - (w i - w (i - 1)) ≤
        -δ * w i)
    (hΦ0 : ∀ k, Phi lam d s w k 0 ≤ Φ0)
    (hΦlim : Tendsto (fun k => Phi lam d s w k 0) atTop (𝓝 Φ0)) :
    ∀ t, 0 ≤ t → ∀ k, Phi lam d s w k t ≤ Φ0 * Real.exp (-δ * t) := by
  intro t ht k
  have hd1 : 1 ≤ d := by omega
  have hr0 : 0 < r := by linarith
  have hrl0 : 0 ≤ r * lam := by positivity
  have hπ : ∀ j, r ^ j * fixedPoint lam d j ≤ (r * lam) ^ j := fun j => by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left (fp_le_pow d hlam0 hlam1 hd1 j) (pow_nonneg hr0.le j)
  have hsε : ∀ u j, s u j ≤ |eps lam d s j u| + fixedPoint lam d j := by
    intro u j; unfold eps; linarith [le_abs_self (s u j - fixedPoint lam d j)]
  have hΦ00 : 0 ≤ Φ0 := le_trans (Phi_nonneg w hw 0 0) (hΦ0 0)
  have hrlpos : 0 < 1 - r * lam := by linarith
  set B0 := r ^ I * Φ0 + 1 / (1 - r * lam) with hB0def
  have hB00 : 0 ≤ B0 := add_nonneg (mul_nonneg (pow_nonneg hr0.le I) hΦ00)
    (div_nonneg zero_le_one hrlpos.le)
  have hB0 : ∀ m, Usum s r m 0 ≤ B0 := by
    intro m
    unfold Usum
    calc ∑ i ∈ range m, r ^ (i + 1) * s 0 (i + 1)
        ≤ ∑ i ∈ range m, (r ^ I * (w (i + 1) * |eps lam d s (i + 1) 0|) + (r * lam) ^ (i + 1)) := by
          apply Finset.sum_le_sum; intro i _
          have h1 := hsε 0 (i + 1)
          have h2 := hrw (i + 1) (by omega)
          have h3 := hπ (i + 1)
          have hrp := pow_pos hr0 (i + 1)
          calc r ^ (i + 1) * s 0 (i + 1)
              ≤ r ^ (i + 1) * (|eps lam d s (i + 1) 0| + fixedPoint lam d (i + 1)) :=
                mul_le_mul_of_nonneg_left h1 hrp.le
            _ = r ^ (i + 1) * |eps lam d s (i + 1) 0| + r ^ (i + 1) * fixedPoint lam d (i + 1) := by
                ring
            _ ≤ r ^ I * w (i + 1) * |eps lam d s (i + 1) 0| + (r * lam) ^ (i + 1) :=
                add_le_add (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)) h3
            _ = _ := by ring
      _ = r ^ I * Phi lam d s w m 0 + ∑ i ∈ range m, (r * lam) ^ (i + 1) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]; rfl
      _ ≤ B0 := add_le_add (mul_le_mul_of_nonneg_left (hΦ0 m) (pow_nonneg hr0.le I))
          (geom_partial_le hrl0 hrl m)
  obtain ⟨K, hK0, hKb⟩ := U_bound hd1 hs hlam0 r hr1.le B0 hB00 hB0 t
  set τ : ℕ → ℝ := fun n => r ^ n * s 0 n + lam * K ^ 2 * r ^ 2 / r ^ n * t with hτdef
  set γ : ℕ → ℝ := fun n => 2 / r ^ I * (τ n + (r * lam) ^ n) with hγdef
  have hτ : ∀ n, 2 ≤ n → ∀ u ∈ Set.Icc 0 t, r ^ n * s u n ≤ τ n := by
    intro n hn u hu
    have h1 := tail_bound hd hs hlam0 r hr1.le K t hKb n hn u hu
    have h2 : lam * K ^ 2 * r ^ 2 / r ^ n * u ≤ lam * K ^ 2 * r ^ 2 / r ^ n * t :=
      mul_le_mul_of_nonneg_left hu.2 (div_nonneg (by positivity) (pow_pos hr0 n).le)
    simp only [hτdef]; linarith
  have hτ0 : ∀ n, 0 ≤ τ n := fun n => add_nonneg
    (mul_nonneg (pow_nonneg hr0.le _) (st_nonneg hs le_rfl n))
    (mul_nonneg (div_nonneg (by positivity) (pow_pos hr0 n).le) ht)
  have hγ0 : ∀ n, 0 ≤ γ n := fun n =>
    mul_nonneg (div_nonneg zero_le_two (pow_pos hr0 I).le) (add_nonneg (hτ0 n) (pow_nonneg hrl0 n))
  have hbd : ∀ n, max I 2 ≤ n → ∀ u ∈ Set.Icc 0 t, w n * |eps lam d s (n + 1) u| ≤ γ n := by
    intro n hn u hu
    have hu0 := hu.1
    have e1 : |eps lam d s (n + 1) u| ≤ s u n + fixedPoint lam d n := by
      unfold eps
      have a := st_nonneg hs hu0 (n + 1)
      have b := (fp_pos d hlam0 (n + 1)).le
      have c := st_anti hs hu0 (Nat.le_succ n)
      have e := fp_anti d hlam0 hlam1 hd1 (Nat.le_succ n)
      rw [abs_le]; constructor <;> linarith
    have hwn' := hwn n (le_trans (le_max_left _ _) hn)
    have hτn := hτ n (le_trans (le_max_right _ _) hn) u hu
    calc w n * |eps lam d s (n + 1) u| ≤ (2 / r ^ I * r ^ n) * (s u n + fixedPoint lam d n) :=
          mul_le_mul hwn' e1 (abs_nonneg _) (by positivity)
      _ = 2 / r ^ I * (r ^ n * s u n + r ^ n * fixedPoint lam d n) := by ring
      _ ≤ γ n := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg zero_le_two (pow_pos hr0 I).le)
          exact add_le_add hτn (hπ n)
  have hmain : ∀ n, max I 2 ≤ n → Phi lam d s w n t ≤ Φ0 * Real.exp (-δ * t) + γ n / δ := by
    intro n hn
    have hg := gron (f := Phi lam d s w n) (D := DPhi lam d s w n) (T := t) (K := -δ) (ε := γ n)
      (δ0 := Phi lam d s w n 0) (Phi_cont hs w n t) (fun x hx => Phi_hasDeriv hs w n hx.1) le_rfl
      (by
        intro x hx
        have h1 := DPhi_le hlam0 hlam1 hd1 hs w δ hw0 hw coef n hx.1
        have h2 := hbd n hn x ⟨hx.1, hx.2.le⟩
        linarith) t ⟨ht, le_rfl⟩
    rw [gronwallBound_of_K_ne_0 (by linarith : -δ ≠ 0)] at hg
    simp only at hg
    have he : 0 < Real.exp (-δ * t) := Real.exp_pos _
    have he1 : Real.exp (-δ * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h1 : Phi lam d s w n 0 * Real.exp (-δ * t) ≤ Φ0 * Real.exp (-δ * t) :=
      mul_le_mul_of_nonneg_right (hΦ0 n) he.le
    have h2 : γ n / -δ * (Real.exp (-δ * t) - 1) ≤ γ n / δ := by
      have e : γ n / -δ * (Real.exp (-δ * t) - 1) = γ n / δ * (1 - Real.exp (-δ * t)) := by
        rw [div_neg]; ring
      rw [e]
      have : 0 ≤ γ n / δ := div_nonneg (hγ0 n) hδ.le
      nlinarith
    linarith
  have hmono : ∀ n, k ≤ n → Phi lam d s w k t ≤ Phi lam d s w n t := by
    intro n hkn
    unfold Phi
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hkn)
      (fun i _ _ => mul_nonneg (hw _) (abs_nonneg _))
  have hgeo : Tendsto (fun n => (r * lam) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hrl0 hrl
  have hγlim : Tendsto γ atTop (𝓝 0) := by
    have hA : Tendsto (fun n => r ^ n * s 0 n) atTop (𝓝 0) := by
      rw [← tendsto_add_atTop_iff_nat 1]
      have hdiff : Tendsto (fun n => Phi lam d s w (n + 1) 0 - Phi lam d s w n 0) atTop (𝓝 0) := by
        have := ((tendsto_add_atTop_iff_nat 1).mpr hΦlim).sub hΦlim
        simpa using this
      have hup : Tendsto (fun n => r ^ I * (Phi lam d s w (n + 1) 0 - Phi lam d s w n 0) +
          (r * lam) ^ (n + 1)) atTop (𝓝 0) := by
        have := (hdiff.const_mul (r ^ I)).add ((tendsto_add_atTop_iff_nat 1).mpr hgeo)
        simpa using this
      apply squeeze_zero (fun n => mul_nonneg (pow_nonneg hr0.le _) (st_nonneg hs le_rfl _)) _ hup
      intro n
      have e : Phi lam d s w (n + 1) 0 - Phi lam d s w n 0 = w (n + 1) * |eps lam d s (n + 1) 0| := by
        unfold Phi; rw [Finset.sum_range_succ]; ring
      rw [e]
      have h1 := hsε 0 (n + 1)
      have h2 := hrw (n + 1) (by omega)
      have h3 := hπ (n + 1)
      calc r ^ (n + 1) * s 0 (n + 1)
          ≤ r ^ (n + 1) * (|eps lam d s (n + 1) 0| + fixedPoint lam d (n + 1)) :=
            mul_le_mul_of_nonneg_left h1 (pow_pos hr0 _).le
        _ = r ^ (n + 1) * |eps lam d s (n + 1) 0| + r ^ (n + 1) * fixedPoint lam d (n + 1) := by ring
        _ ≤ r ^ I * w (n + 1) * |eps lam d s (n + 1) 0| + (r * lam) ^ (n + 1) :=
            add_le_add (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)) h3
        _ = _ := by ring
    have hB : Tendsto (fun n => lam * K ^ 2 * r ^ 2 / r ^ n * t) atTop (𝓝 0) := by
      have hinv : Tendsto (fun n => (r⁻¹) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hr0.le) (inv_lt_one_of_one_lt₀ hr1)
      have := hinv.const_mul (lam * K ^ 2 * r ^ 2 * t)
      rw [mul_zero] at this
      refine this.congr (fun n => ?_)
      rw [inv_pow]; field_simp
    have hτlim : Tendsto τ atTop (𝓝 0) := by
      have := hA.add hB; simpa using this
    have := (hτlim.add hgeo).const_mul (2 / r ^ I)
    simpa using this
  have hev : ∀ᶠ n in atTop, Phi lam d s w k t ≤ Φ0 * Real.exp (-δ * t) + γ n / δ := by
    filter_upwards [eventually_ge_atTop (max k (max I 2))] with n hn
    exact le_trans (hmono n (le_trans (le_max_left _ _) hn)) (hmain n (le_trans (le_max_right _ _) hn))
  have hlim2 : Tendsto (fun n => Φ0 * Real.exp (-δ * t) + γ n / δ) atTop
      (𝓝 (Φ0 * Real.exp (-δ * t))) := by
    have := (hγlim.div_const δ).const_add (Φ0 * Real.exp (-δ * t))
    simpa using this
  exact ge_of_tendsto hlim2 hev

end main

end StrictCompatLB.MeanField.T411

open StrictCompatLB.MeanField StrictCompatLB.MeanField.T411 PowerTwoChoices.Limit in
theorem solution (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 2 ≤ d) :
    ∃ ω : ℕ → ℝ, (∀ i, 1 ≤ i → 0 < ω i) ∧ ∃ r : ℝ, 1 < r ∧ r < 2 / (1 + lam) ∧
      (∀ i : ℕ, 1 ≤ i → ω (i0Index lam d + i) = ω (i0Index lam d) * r ^ i) ∧
      ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
        (∀ t : ℝ, 0 ≤ t → InY (s t)) →
        PowerTwoChoices.Limit.potential lam d ω (s 0) < ⊤ →
        PowerTwoChoices.Limit.ConvergesExponentially
          (fun t => PowerTwoChoices.Limit.potential lam d ω (s t)) := by
  have hd1 : 1 ≤ d := by omega
  set I := i0Index lam d with hIdef
  obtain ⟨hI, hIc⟩ := i0_spec d hlam0 hlam1 hd1
  rw [← hIdef] at hI hIc
  have hπI := fp_i0_le_half d hlam0 hlam1 hd1
  rw [← hIdef] at hπI
  set θ := lam * (1 + 2 * fixedPoint lam d I) with hθdef
  have hθ : θ < (1 + lam) / 2 := by rw [hθdef]; linarith
  have hθ1 : θ < 1 := by linarith
  have hθ0 : 0 < θ := by
    rw [hθdef]; have := fp_pos d hlam0 I; positivity
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set c := max (2 * lam * d) 2 with hcdef
  have hc2 : 2 ≤ c := le_max_right _ _
  have hcl : 2 * lam * d ≤ c := le_max_left _ _
  set q := c⁻¹ with hqdef
  have hq0 : 0 < q := inv_pos.mpr (by linarith)
  have hq : q ≤ 1 / 2 := by
    rw [hqdef]; rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
  have hdq : lam * d * q ≤ 1 / 2 := by
    rw [hqdef, ← div_eq_mul_inv, div_le_iff₀ (by linarith)]; linarith
  set A := q ^ (I - 1) with hAdef
  have hA0 : 0 < A := pow_pos hq0 _
  have hl1 : 1 < 2 / (1 + lam) := by rw [lt_div_iff₀ (by linarith)]; linarith
  have h1θ : 1 < 1 / θ := by rw [lt_div_iff₀ hθ0]; linarith
  set η := min (min (A / (4 * lam * d + 1)) ((1 / θ - 1) / 2)) ((2 / (1 + lam) - 1) / 2) with hηdef
  have hη0 : 0 < η := by
    apply lt_min (lt_min (div_pos hA0 (by positivity)) (by linarith)) (by linarith)
  have hη1 : η ≤ A / (4 * lam * d + 1) := le_trans (min_le_left _ _) (min_le_left _ _)
  have hη2 : η ≤ (1 / θ - 1) / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hη3 : η ≤ (2 / (1 + lam) - 1) / 2 := min_le_right _ _
  set r := 1 + η with hrdef
  have hr1 : 1 < r := by linarith
  have hr2 : r < 2 / (1 + lam) := by linarith
  have hrA : 2 * lam * d * (r - 1) ≤ A / 2 := by
    rw [hrdef, add_sub_cancel_left]
    have hpos : 0 < 4 * lam * d + 1 := by positivity
    have : η * (4 * lam * d + 1) ≤ A := by rwa [le_div_iff₀ hpos] at hη1
    have : 0 ≤ 2 * lam * d * η := by positivity
    nlinarith
  have hrθ : r * θ < 1 := by
    have : r ≤ 1 + (1 / θ - 1) / 2 := by linarith
    have h2 : (1 + (1 / θ - 1) / 2) * θ = (1 + θ) / 2 := by field_simp; ring
    calc r * θ ≤ (1 + (1 / θ - 1) / 2) * θ := mul_le_mul_of_nonneg_right this hθ0.le
      _ = (1 + θ) / 2 := h2
      _ < 1 := by linarith
  have hrl : r * lam < 1 := by
    have : r * (1 + lam) < 2 := by rwa [lt_div_iff₀ (by linarith)] at hr2
    nlinarith
  set δ := min (A / 4) ((r - 1) * (1 - r * θ) / r) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (div_pos (mul_pos (by linarith) (by linarith)) (by linarith))
  set w := wt I q r with hwdef
  have hw1 : ∀ i, 1 ≤ i → 1 ≤ w i := fun i hi => wt_ge_one I q r hI hq0 hq hr1.le i hi
  have hw0 : w 0 = 0 := wt_zero I q r
  have hw : ∀ i, 0 ≤ w i := by
    intro i; rcases Nat.eq_zero_or_pos i with h | h
    · rw [h, hw0]
    · linarith [hw1 i h]
  refine ⟨w, fun i hi => by linarith [hw1 i hi], r, hr1, hr2, fun i hi => ?_, ?_⟩
  · rw [hwdef, wt_high I q r hI hq0 hq hr1.le (I + i) (by omega), Nat.add_sub_cancel_left]
  intro s hs _ hfin
  have hrw : ∀ j, 1 ≤ j → r ^ j ≤ r ^ I * w j := by
    intro j hj
    by_cases hjI : j ≤ I
    · have h1 : r ^ j ≤ r ^ I := pow_le_pow_right₀ hr1.le hjI
      have h2 := hw1 j hj
      have : 0 ≤ r ^ I := by positivity
      nlinarith
    · push Not at hjI
      rw [hwdef, wt_high I q r hI hq0 hq hr1.le j hjI.le]
      have h2 := hw1 I hI
      have e : r ^ j = r ^ I * r ^ (j - I) := by rw [← pow_add]; congr 1; omega
      rw [e]
      have : 0 ≤ r ^ I * r ^ (j - I) := by positivity
      nlinarith
  have hwn : ∀ n, I ≤ n → w n ≤ 2 / r ^ I * r ^ n := by
    intro n hn
    rw [hwdef, wt_high I q r hI hq0 hq hr1.le n hn]
    have h2 := wt_I_le_two I q r hI hq0 hq hr1.le
    have e : 2 / r ^ I * r ^ n = 2 * r ^ (n - I) := by
      have : r ^ n = r ^ I * r ^ (n - I) := by rw [← pow_add]; congr 1; omega
      rw [this]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have coef : ∀ t, 0 ≤ t → ∀ i, 1 ≤ i →
      lam * hpoly d (s t i) (fixedPoint lam d i) * (w (i + 1) - w i) - (w i - w (i - 1)) ≤
        -δ * w i := by
    intro t ht i hi
    apply coeff_ineq I q r hI hq0 hq hr1.le lam θ δ d hlam0 hdq hr1 hrA hrθ (min_le_left _ _)
      (min_le_right _ _) i hi
    · exact hpoly_nonneg d (st_nonneg hs ht i) (fp_pos d hlam0 i).le
    · exact hpoly_le_d d (st_nonneg hs ht i) (st_le_one hs ht i) (fp_pos d hlam0 i).le
        (fp_le_one d hlam0 hlam1 hd1 i)
    · intro hIi
      have hπi : fixedPoint lam d i ≤ fixedPoint lam d I := fp_anti d hlam0 hlam1 hd1 hIi.le
      have hh := hpoly_le_small d hd1 (st_nonneg hs ht i) (st_le_one hs ht i)
        (fp_pos d hlam0 i).le (le_trans hπi hπI)
      rw [hθdef]
      calc lam * hpoly d (s t i) (fixedPoint lam d i) ≤ lam * (1 + 2 * fixedPoint lam d i) :=
            mul_le_mul_of_nonneg_left hh hlam0.le
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left _ hlam0.le; linarith
  -- partial sums of the potential
  have hpart : ∀ t k, ∑ i ∈ range (k + 1),
      (if 1 ≤ i then ENNReal.ofReal (w i * |s t i - fixedPoint lam d i|) else 0) =
        ENNReal.ofReal (Phi lam d s w k t) := by
    intro t k
    rw [Finset.sum_range_succ']
    simp only [show ¬ (1 ≤ 0) by omega, if_false, add_zero,
      show ∀ i : ℕ, 1 ≤ i + 1 from fun i => by omega, if_true]
    unfold Phi eps
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw _) (abs_nonneg _))]
  have hfin' : potential lam d w (s 0) ≠ ⊤ := hfin.ne
  set Φ0 := (potential lam d w (s 0)).toReal with hΦ0def
  have hΦ0 : ∀ k, Phi lam d s w k 0 ≤ Φ0 := by
    intro k
    rw [hΦ0def, ← ENNReal.ofReal_le_iff_le_toReal hfin', ← hpart 0 k]
    exact ENNReal.sum_le_tsum _
  have hΦlim : Tendsto (fun k => Phi lam d s w k 0) atTop (𝓝 Φ0) := by
    have h1 := ENNReal.tendsto_nat_tsum
      (fun i => if 1 ≤ i then ENNReal.ofReal (w i * |s 0 i - fixedPoint lam d i|) else 0)
    have h2 := (tendsto_add_atTop_iff_nat 1).mpr h1
    simp only [hpart 0] at h2
    have h3 := (ENNReal.tendsto_toReal hfin').comp h2
    refine h3.congr (fun k => ?_)
    simp only [Function.comp]
    exact ENNReal.toReal_ofReal (Phi_nonneg w hw k 0)
  have hest := main_estimate hlam0 hlam1 hd hs w I r δ Φ0 hr1 hrl hδ0 hw0 hw hrw hwn coef hΦ0 hΦlim
  refine ⟨δ, hδ0, Φ0, fun t ht => ?_⟩
  show potential lam d w (s t) ≤ _
  unfold potential
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro n
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0]; simp
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [hpart t k]
    exact ENNReal.ofReal_le_ofReal (hest t ht k)
