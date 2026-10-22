-- Prove2me | solution 1 for ShockWear.RandThreshold.theorem31_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:50:14.939349+00:00
-- url     : https://prove2.me/submissions/2e4bf0d5-262c-4b37-ac4a-a7669b460f8a

import Mathlib
import Definitions.Def_ShockWear_RandThreshold_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace SWP
open ShockWear.RandThreshold Filter Topology

lemma poisW_nonneg {lam t : ℝ} (h : 0 ≤ lam * t) (k : ℕ) : 0 ≤ poisW lam t k := by
  unfold poisW; positivity

lemma exp_hasSum (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rwa [← Real.exp_eq_exp_ℝ] at this

lemma poisW_hasSum (lam t : ℝ) : HasSum (poisW lam t) 1 := by
  have h := (exp_hasSum (lam * t)).mul_left (Real.exp (-(lam * t)))
  have e : Real.exp (-(lam * t)) * Real.exp (lam * t) = 1 := by
    rw [← Real.exp_add]; simp
  rw [e] at h
  have e2 : poisW lam t = fun k : ℕ => Real.exp (-(lam * t)) * ((lam * t) ^ k / (k.factorial : ℝ)) := by
    funext k; unfold poisW; ring
  rw [e2]; exact h

lemma summable_mul_poisW {lam t : ℝ} (h : 0 ≤ lam * t) {a : ℕ → ℝ} (ha : ∀ k, |a k| ≤ 1) :
    Summable (fun k => a k * poisW lam t k) := by
  refine Summable.of_norm_bounded (poisW_hasSum lam t).summable ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poisW_nonneg h k)]
  calc |a k| * poisW lam t k ≤ 1 * poisW lam t k :=
        mul_le_mul_of_nonneg_right (ha k) (poisW_nonneg h k)
    _ = poisW lam t k := one_mul _

lemma summable_norm_mul_poisW {lam t : ℝ} (h : 0 ≤ lam * t) {a : ℕ → ℝ} (ha : ∀ k, |a k| ≤ 1) :
    Summable (fun k => ‖a k * poisW lam t k‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (poisW_hasSum lam t).summable
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poisW_nonneg h k)]
  calc |a k| * poisW lam t k ≤ 1 * poisW lam t k :=
        mul_le_mul_of_nonneg_right (ha k) (poisW_nonneg h k)
    _ = poisW lam t k := one_mul _

lemma surv_eq {lam : ℝ} {P : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    shockSurv lam P t = ∑' k, P k * poisW lam t k := by
  unfold shockSurv; rw [if_neg (not_lt.2 ht)]

lemma surv_zero (lam : ℝ) (P : ℕ → ℝ) : shockSurv lam P 0 = P 0 := by
  rw [surv_eq le_rfl]
  rw [tsum_eq_single 0 (fun k hk => by simp [poisW, hk])]
  simp [poisW]

lemma Pbound {P : ℕ → ℝ} (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k) :
    ∀ k, |P k| ≤ 1 := by
  intro k
  rw [abs_of_nonneg (hnn k)]
  exact (hanti (Nat.zero_le k)).trans hP0

theorem eq26_core (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 ≤ 1) (hanti : Antitone P)
    (hnn : ∀ k, 0 ≤ P k) :
    ∀ t, 0 ≤ t → shockSurv lam P 0 * Real.exp (-(lam * t)) ≤ shockSurv lam P t := by
  intro t ht
  have hlt : 0 ≤ lam * t := mul_nonneg hlam.le ht
  rw [surv_zero, surv_eq ht]
  have hs := summable_mul_poisW hlt (Pbound hP0 hanti hnn)
  have h1 : P 0 * poisW lam t 0 ≤ ∑' k, P k * poisW lam t k :=
    hs.le_tsum 0 (fun j _ => mul_nonneg (hnn j) (poisW_nonneg hlt j))
  have h2 : poisW lam t 0 = Real.exp (-(lam * t)) := by simp [poisW]
  rw [h2] at h1
  exact h1

lemma surv_bounds {lam : ℝ} (hlam : 0 < lam) {P : ℕ → ℝ} (hP0 : P 0 ≤ 1) (hanti : Antitone P)
    (hnn : ∀ k, 0 ≤ P k) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ shockSurv lam P t ∧ shockSurv lam P t ≤ 1 := by
  have hlt : 0 ≤ lam * t := mul_nonneg hlam.le ht
  rw [surv_eq ht]
  refine ⟨tsum_nonneg (fun k => mul_nonneg (hnn k) (poisW_nonneg hlt k)), ?_⟩
  have hs := summable_mul_poisW hlt (Pbound hP0 hanti hnn)
  have h1 : ∑' k, P k * poisW lam t k ≤ ∑' k, poisW lam t k := by
    refine hs.tsum_le_tsum (fun k => ?_) (poisW_hasSum lam t).summable
    calc P k * poisW lam t k ≤ 1 * poisW lam t k :=
          mul_le_mul_of_nonneg_right ((hanti (Nat.zero_le k)).trans hP0) (poisW_nonneg hlt k)
      _ = poisW lam t k := one_mul _
  rw [(poisW_hasSum lam t).tsum_eq] at h1
  exact h1

theorem transfer_eq (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 ≤ 1) (hanti : Antitone P)
    (hnn : ∀ k, 0 ≤ P k) (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    ∀ t, 0 ≤ t → shockSurv lam P t - Real.exp (-((1 - ζ) * lam * t)) =
        ∑' k, (P k - ζ ^ k) * poisW lam t k := by
  intro t ht
  have hlt : 0 ≤ lam * t := mul_nonneg hlam.le ht
  have hs := summable_mul_poisW hlt (Pbound hP0 hanti hnn)
  have hz : HasSum (fun k => ζ ^ k * poisW lam t k) (Real.exp (-((1 - ζ) * lam * t))) := by
    have h := (exp_hasSum (ζ * (lam * t))).mul_left (Real.exp (-(lam * t)))
    have e : Real.exp (-(lam * t)) * Real.exp (ζ * (lam * t)) = Real.exp (-((1 - ζ) * lam * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e] at h
    have e2 : (fun k : ℕ => ζ ^ k * poisW lam t k) =
        fun k : ℕ => Real.exp (-(lam * t)) * ((ζ * (lam * t)) ^ k / (k.factorial : ℝ)) := by
      funext k; unfold poisW; rw [mul_pow]; ring
    rw [e2]; exact h
  have h2 := hs.hasSum.sub hz
  rw [surv_eq ht]
  have e3 : (fun k => (P k - ζ ^ k) * poisW lam t k) =
      fun k => P k * poisW lam t k - ζ ^ k * poisW lam t k := by
    funext k; ring
  rw [e3]
  exact h2.tsum_eq.symm

lemma poisW_conv (lam t x : ℝ) (n : ℕ) :
    poisW lam (t + x) n = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, poisW lam t kl.1 * poisW lam x kl.2 := by
  unfold poisW
  have h1 : (lam * (t + x)) ^ n =
      ∑ m ∈ Finset.HasAntidiagonal.antidiagonal n, n.choose m.1 • ((lam * t) ^ m.1 * (lam * x) ^ m.2) := by
    rw [mul_add]; exact (Commute.all (lam * t) (lam * x)).add_pow' n
  have h2 : Real.exp (-(lam * (t + x))) = Real.exp (-(lam * t)) * Real.exp (-(lam * x)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, h2, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hm
  have hc : (n.choose m.1 : ℝ) * (m.1.factorial : ℝ) * (m.2.factorial : ℝ) = (n.factorial : ℝ) := by
    have h3 := Nat.choose_mul_factorial_mul_factorial (show m.1 ≤ n by omega)
    have h4 : n - m.1 = m.2 := by omega
    rw [h4] at h3
    exact_mod_cast h3
  have hcn : (n.choose m.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show m.1 ≤ n by omega)).ne'
  have hf1 : (m.1.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hf2 : (m.2.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [nsmul_eq_mul, ← hc]
  field_simp

theorem nbu_core (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 = 1)
    (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k) (hsub : ∀ j k, P (j + k) ≤ P j * P k) :
    IsNBU (shockSurv lam P) := by
  intro x t hx ht
  have hxt : 0 ≤ t + x := add_nonneg ht hx
  have hP := Pbound hP0.le hanti hnn
  have hlx : 0 ≤ lam * x := mul_nonneg hlam.le hx
  have hlt : 0 ≤ lam * t := mul_nonneg hlam.le ht
  have hlxt : 0 ≤ lam * (t + x) := mul_nonneg hlam.le hxt
  rw [surv_eq hxt, surv_eq hx, surv_eq ht,
    mul_comm (∑' k, P k * poisW lam x k) (∑' k, P k * poisW lam t k)]
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_mul_poisW hlt hP)
    (summable_norm_mul_poisW hlx hP)]
  refine (summable_mul_poisW hlxt hP).tsum_le_tsum (fun n => ?_) ?_
  · rw [poisW_conv, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro kl hkl
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    have h1 := hsub kl.1 kl.2
    rw [hkl] at h1
    have h2 : 0 ≤ poisW lam t kl.1 * poisW lam x kl.2 :=
      mul_nonneg (poisW_nonneg hlt _) (poisW_nonneg hlx _)
    calc P n * (poisW lam t kl.1 * poisW lam x kl.2)
        ≤ (P kl.1 * P kl.2) * (poisW lam t kl.1 * poisW lam x kl.2) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = P kl.1 * poisW lam t kl.1 * (P kl.2 * poisW lam x kl.2) := by ring
  · exact (summable_norm_sum_mul_antidiagonal_of_summable_norm (summable_norm_mul_poisW hlt hP)
      (summable_norm_mul_poisW hlx hP)).of_norm

end SWP

theorem solution (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 = 1)
    (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hsub : ∀ j k, P (j + k) ≤ P j * P k) :
    ShockWear.RandThreshold.IsNBU (ShockWear.RandThreshold.shockSurv lam P) :=
  SWP.nbu_core lam hlam P hP0 hanti hnn hsub
