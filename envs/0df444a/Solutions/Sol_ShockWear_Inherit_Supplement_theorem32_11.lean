-- Prove2me | solution 1 for ShockWear.Inherit.Supplement.theorem32_11
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:27.476373+00:00
-- url     : https://prove2.me/submissions/05afd7f0-2838-42c1-9e6d-0409d1d2d6ed

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_Inherit_Supplement_ReversedAgeing

open ShockWear
open ShockWear.Inherit
open ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem solution (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hprod : ∀ j k, P j * P k ≤ P (k + j)) :
    IsNWU (ShockWear.CumDamage.shockSurv lam P) := by
      intro x t hx ht
      have hle1 : ∀ k, P k ≤ 1 := fun k => (hanti (Nat.zero_le k)).trans hP0
      have hWnn : ∀ s, 0 ≤ s → ∀ k, 0 ≤ ShockWear.CumDamage.poisW lam s k := by
        intro s hs k
        unfold ShockWear.CumDamage.poisW
        have : 0 ≤ lam * s := mul_nonneg hlam.le hs
        positivity
      have hWsum : ∀ s, Summable (fun k => ShockWear.CumDamage.poisW lam s k) := by
        intro s
        have := (Real.summable_pow_div_factorial (lam * s)).mul_left (Real.exp (-(lam * s)))
        refine this.congr (fun k => ?_)
        unfold ShockWear.CumDamage.poisW
        ring
      have hTsum : ∀ s, 0 ≤ s → Summable (fun k => P k * ShockWear.CumDamage.poisW lam s k) := by
        intro s hs
        refine (hWsum s).of_nonneg_of_le (fun k => mul_nonneg (hnn k) (hWnn s hs k)) (fun k => ?_)
        calc P k * ShockWear.CumDamage.poisW lam s k ≤ 1 * ShockWear.CumDamage.poisW lam s k :=
              mul_le_mul_of_nonneg_right (hle1 k) (hWnn s hs k)
          _ = _ := one_mul _
      have hbinom : ∀ n : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          ShockWear.CumDamage.poisW lam x p.1 * ShockWear.CumDamage.poisW lam t p.2
            = ShockWear.CumDamage.poisW lam (t + x) n := by
        intro n
        unfold ShockWear.CumDamage.poisW
        have hadd : lam * (t + x) = lam * x + lam * t := by ring
        rw [hadd, (Commute.all (lam * x) (lam * t)).add_pow', Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        subst hp
        have hf := Nat.add_choose_mul_factorial_mul_factorial p.1 p.2
        rw [← Nat.choose_symm_add] at hf
        have hf' : ((p.1 + p.2).choose p.1 : ℝ) * (p.1.factorial : ℝ) * (p.2.factorial : ℝ)
            = ((p.1 + p.2).factorial : ℝ) := by exact_mod_cast hf
        rw [nsmul_eq_mul, ← hf', Real.exp_neg, Real.exp_neg, Real.exp_neg, Real.exp_add]
        have h1 : (p.1.factorial : ℝ) ≠ 0 := by positivity
        have h2 : (p.2.factorial : ℝ) ≠ 0 := by positivity
        have h3 : ((p.1 + p.2).choose p.1 : ℝ) ≠ 0 := by
          have := Nat.choose_pos (Nat.le_add_right p.1 p.2)
          positivity
        rw [mul_inv]
        generalize (Real.exp (lam * x))⁻¹ = e1 at *
        generalize (Real.exp (lam * t))⁻¹ = e2 at *
        generalize (lam * x) ^ p.1 = u at *
        generalize (lam * t) ^ p.2 = v at *
        generalize ((p.1 + p.2).choose p.1 : ℝ) = a at *
        generalize (p.1.factorial : ℝ) = b at *
        generalize (p.2.factorial : ℝ) = c at *
        field_simp
      have htx : 0 ≤ t + x := add_nonneg ht hx
      unfold ShockWear.CumDamage.shockSurv
      rw [if_neg (not_lt.mpr hx), if_neg (not_lt.mpr ht), if_neg (not_lt.mpr htx)]
      have hnorm : ∀ s, 0 ≤ s → Summable (fun k => ‖P k * ShockWear.CumDamage.poisW lam s k‖) := by
        intro s hs
        refine (hTsum s hs).congr (fun k => ?_)
        rw [Real.norm_of_nonneg (mul_nonneg (hnn k) (hWnn s hs k))]
      rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (hnorm x hx) (hnorm t ht)]
      have hterm : ∀ n : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          P p.1 * ShockWear.CumDamage.poisW lam x p.1 * (P p.2 * ShockWear.CumDamage.poisW lam t p.2)
            ≤ P n * ShockWear.CumDamage.poisW lam (t + x) n := by
        intro n
        rw [← hbinom n, Finset.mul_sum]
        refine Finset.sum_le_sum (fun p hp => ?_)
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        have hq := hprod p.1 p.2
        rw [add_comm, hp] at hq
        have := mul_nonneg (hWnn x hx p.1) (hWnn t ht p.2)
        calc P p.1 * ShockWear.CumDamage.poisW lam x p.1 * (P p.2 * ShockWear.CumDamage.poisW lam t p.2)
            = (P p.1 * P p.2) * (ShockWear.CumDamage.poisW lam x p.1 * ShockWear.CumDamage.poisW lam t p.2) := by ring
          _ ≤ P n * (ShockWear.CumDamage.poisW lam x p.1 * ShockWear.CumDamage.poisW lam t p.2) :=
              mul_le_mul_of_nonneg_right hq this
      have hs1 : Summable (fun n : ℕ => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          P p.1 * ShockWear.CumDamage.poisW lam x p.1 * (P p.2 * ShockWear.CumDamage.poisW lam t p.2)) :=
        (hTsum (t + x) htx).of_nonneg_of_le (fun n => Finset.sum_nonneg (fun p _ =>
          mul_nonneg (mul_nonneg (hnn p.1) (hWnn x hx p.1)) (mul_nonneg (hnn p.2) (hWnn t ht p.2)))) hterm
      exact hs1.tsum_le_tsum hterm (hTsum (t + x) htx)
