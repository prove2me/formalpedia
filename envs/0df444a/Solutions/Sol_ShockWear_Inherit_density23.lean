-- Prove2me | solution 1 for ShockWear.Inherit.density23
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:42:47.169105+00:00
-- url     : https://prove2.me/submissions/3c001a4b-b273-404c-b611-a1d861285a9c

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

set_option autoImplicit false
open ShockWear.CumDamage ShockWear.Inherit

/-- the shifted Poisson weight: `w_{k-1}` for `k ≥ 1`, and `0` for `k = 0` -/
noncomputable def sw_wm (lam t : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => poisW lam t k

theorem sw_exp_deriv (lam t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(lam * t))) (-(lam * Real.exp (-(lam * t)))) t := by
  have := (((hasDerivAt_id' t).const_mul lam).neg).exp
  refine this.congr_deriv ?_
  simp <;> ring

theorem sw_w_deriv (lam t : ℝ) (k : ℕ) :
    HasDerivAt (fun t => poisW lam t k) (lam * (sw_wm lam t k - poisW lam t k)) t := by
  cases k with
  | zero =>
    have h1 := sw_exp_deriv lam t
    have : (fun t => poisW lam t 0) = fun t => Real.exp (-(lam * t)) := by
      funext t; simp [poisW]
    rw [this]
    refine h1.congr_deriv ?_
    simp [sw_wm, poisW]
  | succ k =>
    have h1 := sw_exp_deriv lam t
    have h2 : HasDerivAt (fun t : ℝ => (lam * t) ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * (lam * t) ^ k * lam) t := by
      have := ((hasDerivAt_id' t).const_mul lam).pow (k + 1)
      refine this.congr_deriv ?_
      simp <;> ring
    have h3 : HasDerivAt (fun t => poisW lam t (k + 1)) _ t :=
      (h1.mul h2).div_const (((k + 1).factorial : ℕ) : ℝ)
    refine h3.congr_deriv ?_
    have hf : ((k + 1).factorial : ℝ) = (k + 1) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    simp only [sw_wm, poisW]
    rw [hf]
    push_cast
    field_simp
    ring

theorem sw_summable_w (lam t : ℝ) : Summable (fun k => poisW lam t k) := by
  unfold poisW
  have := (Real.summable_pow_div_factorial (lam * t)).mul_left (Real.exp (-(lam * t)))
  refine this.congr fun k => ?_
  ring

theorem sw_summable_wm (lam t : ℝ) : Summable (fun k => sw_wm lam t k) := by
  rw [← summable_nat_add_iff 1]
  simpa [sw_wm] using sw_summable_w lam t

noncomputable def sw_sh (B : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => B ^ k / (k.factorial : ℝ)

theorem sw_w_nonneg (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) (k : ℕ) : 0 ≤ poisW lam t k := by
  unfold poisW
  have : 0 ≤ lam * t := mul_nonneg hlam ht
  positivity

theorem sw_w_le (lam t B : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) (hB : lam * t ≤ B) (k : ℕ) :
    poisW lam t k ≤ B ^ k / (k.factorial : ℝ) := by
  unfold poisW
  have h0 : 0 ≤ lam * t := mul_nonneg hlam ht
  have h1 : Real.exp (-(lam * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have h2 : (lam * t) ^ k ≤ B ^ k := pow_le_pow_left₀ h0 hB k
  have hf : 0 < (k.factorial : ℝ) := by positivity
  rw [div_le_div_iff_of_pos_right hf]
  calc Real.exp (-(lam * t)) * (lam * t) ^ k ≤ 1 * B ^ k :=
        mul_le_mul h1 h2 (pow_nonneg h0 k) zero_le_one
    _ = B ^ k := one_mul _

theorem sw_summable_cw (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) (c : ℕ → ℝ) (C : ℝ)
    (hC : ∀ k, |c k| ≤ C) : Summable (fun k => c k * poisW lam t k) := by
  refine Summable.of_norm_bounded ((sw_summable_w lam t).mul_left C) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sw_w_nonneg lam t hlam ht k)]
  exact mul_le_mul_of_nonneg_right (hC k) (sw_w_nonneg lam t hlam ht k)

theorem sw_deriv (lam : ℝ) (hlam : 0 < lam) (c : ℕ → ℝ) (C : ℝ) (hC : ∀ k, |c k| ≤ C) (t : ℝ)
    (ht : 0 < t) :
    HasDerivAt (fun t => ∑' k, c k * poisW lam t k)
      (lam * ∑' k, (c (k + 1) - c k) * poisW lam t k) t := by
  set B : ℝ := lam * (2 * t) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  let u : ℕ → ℝ := fun k => C * lam * (B ^ k / (k.factorial : ℝ) +
    sw_sh B k)
  have hu : Summable u := by
    refine Summable.mul_left _ (Summable.add (Real.summable_pow_div_factorial B) ?_)
    rw [← summable_nat_add_iff 1]
    simpa [sw_sh] using Real.summable_pow_div_factorial B
  have hbound : ∀ k (y : ℝ), y ∈ Set.Ioo 0 (2 * t) →
      ‖c k * (lam * (sw_wm lam y k - poisW lam y k))‖ ≤ u k := by
    intro k y hy
    have hy0 : 0 ≤ y := hy.1.le
    have hBy : lam * y ≤ B := by
      rw [hBdef]; exact mul_le_mul_of_nonneg_left hy.2.le hlam.le
    have hw := sw_w_le lam y B hlam.le hy0 hBy k
    have hwn := sw_w_nonneg lam y hlam.le hy0 k
    have hm : |sw_wm lam y k| ≤ sw_sh B k := by
      cases k with
      | zero => simp [sw_wm, sw_sh]
      | succ k =>
        simp only [sw_wm, sw_sh]
        rw [abs_of_nonneg (sw_w_nonneg lam y hlam.le hy0 k)]
        exact sw_w_le lam y B hlam.le hy0 hBy k
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hlam]
    have h1 : |sw_wm lam y k - poisW lam y k| ≤ |sw_wm lam y k| + poisW lam y k := by
      calc |sw_wm lam y k - poisW lam y k| ≤ |sw_wm lam y k| + |poisW lam y k| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg hwn]
    have h2 : |sw_wm lam y k - poisW lam y k| ≤
        B ^ k / (k.factorial : ℝ) + sw_sh B k := by
      linarith
    calc |c k| * (lam * |sw_wm lam y k - poisW lam y k|)
        ≤ C * (lam * (B ^ k / (k.factorial : ℝ) +
            sw_sh B k)) :=
          mul_le_mul (hC k) (mul_le_mul_of_nonneg_left h2 hlam.le) (by positivity) hC0
      _ = u k := by simp only [u]; ring
  have hmain := hasDerivAt_tsum_of_isPreconnected (u := u) (t := Set.Ioo 0 (2 * t))
    (g := fun k y => c k * poisW lam y k)
    (g' := fun k y => c k * (lam * (sw_wm lam y k - poisW lam y k)))
    (y₀ := t) (y := t) hu isOpen_Ioo isPreconnected_Ioo
    (fun k y _ => (sw_w_deriv lam y k).const_mul (c k)) hbound ⟨ht, by linarith⟩
    (sw_summable_cw lam t hlam.le ht.le c C hC) ⟨ht, by linarith⟩
  refine hmain.congr_deriv ?_
  have s1 := sw_summable_cw lam t hlam.le ht.le c C hC
  have s2 := sw_summable_cw lam t hlam.le ht.le (fun k => c (k + 1)) C (fun k => hC (k + 1))
  have s3 : Summable (fun n => c n * sw_wm lam t n) := by
    rw [← summable_nat_add_iff 1]
    simpa [sw_wm] using s2
  have e1 : ∑' n, c n * sw_wm lam t n = ∑' k, c (k + 1) * poisW lam t k := by
    rw [s3.tsum_eq_zero_add]
    simp [sw_wm]
  have e2 : ∑' k, (c (k + 1) - c k) * poisW lam t k =
      ∑' k, c (k + 1) * poisW lam t k - ∑' k, c k * poisW lam t k := by
    simp only [sub_mul]
    exact Summable.tsum_sub s2 s1
  have e3 : ∑' n, c n * (lam * (sw_wm lam t n - poisW lam t n)) =
      lam * (∑' n, c n * sw_wm lam t n - ∑' n, c n * poisW lam t n) := by
    rw [← Summable.tsum_sub s3 s1, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    ring
  rw [e3, e2, e1]

theorem solution (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k) :
    ∀ t, 0 < t → HasDerivAt (ShockWear.CumDamage.shockSurv lam P) (-shockDens lam P t) t := by
  intro t ht
  have hP1 : ∀ k, |P k| ≤ 1 := fun k => by
    rw [abs_of_nonneg (hnn k)]; exact le_trans (hanti (Nat.zero_le k)) hP0
  have h := sw_deriv lam hlam P 1 hP1 t ht
  have heq : (ShockWear.CumDamage.shockSurv lam P) =ᶠ[nhds t] fun t => ∑' k, P k * poisW lam t k := by
    filter_upwards [Ioi_mem_nhds ht] with y hy
    have hy' : 0 < y := hy
    simp [ShockWear.CumDamage.shockSurv, not_lt.mpr hy'.le]
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  unfold shockDens
  have : ∀ k, failProb P (k + 1) = -(P (k + 1) - P k) := fun k => by simp [failProb]
  simp only [this, neg_mul, tsum_neg]
  ring
