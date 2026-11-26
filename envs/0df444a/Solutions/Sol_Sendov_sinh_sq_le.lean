-- Prove2me | solution 1 for Sendov.sinh_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:59:16.874783+00:00
-- url     : https://prove2.me/submissions/0c81cbc4-ed63-4a80-a8fe-2849ca765788

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_Sendov_Common_Sinh
section
namespace Sendov
open Real Set Filter
private lemma nonneg_of_deriv {f g : ℝ → ℝ} (hd : ∀ z, HasDerivAt f (g z) z)
    (h0 : f 0 = 0) (hg : ∀ z, 0 ≤ z → 0 ≤ g z) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ f y := by
  have hmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun z _ => (hd z).continuousAt.continuousWithinAt)
      (fun z hz => (hd z).differentiableAt.differentiableWithinAt) (fun z hz => ?_)
    rw [(hd z).deriv]
    rw [interior_Ici] at hz
    exact hg z (le_of_lt hz)
  simpa [h0] using hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hy) hy
private lemma quad_le_exp {y : ℝ} (hy : 0 ≤ y) : 1 + y + y ^ 2 / 2 ≤ exp y := by
  suffices 0 ≤ exp y - 1 - y - y ^ 2 / 2 by linarith
  refine nonneg_of_deriv (f := fun t => exp t - 1 - t - t ^ 2 / 2)
    (g := fun t => exp t - 1 - t) (fun t => ?_) (by norm_num) (fun t ht => ?_) hy
  · exact ((((hasDerivAt_exp t).sub_const 1).sub (hasDerivAt_id' t)).sub
      ((hasDerivAt_pow 2 t).div_const 2)).congr_deriv (by norm_num)
  · linarith [add_one_le_exp t]
private lemma hasDerivAt_Sf (u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ y : ℝ) :
    HasDerivAt (fun t : ℝ => Sf u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ t)
      (Sf (2 * u₃) (2 * u₂ + 3 * u₃) (2 * u₁ + 2 * u₂) (2 * u₀ + u₁)
          v₄ (v₃ + 4 * v₄) (v₂ + 3 * v₃) (v₁ + 2 * v₂) (v₀ + v₁)
          0 (3 * w₃) (2 * w₂) w₁ y) y := by
  simp only [Sf]
  have he2 : HasDerivAt (fun t : ℝ => exp (2 * t)) (exp (2 * y) * 2) y :=
    ((hasDerivAt_id' y).const_mul (2 : ℝ)).exp.congr_deriv (by ring)
  have he1 : HasDerivAt (fun t : ℝ => exp t) (exp y) y := hasDerivAt_exp y
  have hu : HasDerivAt (fun t : ℝ => u₃ * t ^ 3 + u₂ * t ^ 2 + u₁ * t + u₀)
      (3 * u₃ * y ^ 2 + 2 * u₂ * y + u₁) y := by
    have h := ((((hasDerivAt_pow 3 y).const_mul u₃).add
      ((hasDerivAt_pow 2 y).const_mul u₂)).add ((hasDerivAt_id' y).const_mul u₁)).add_const u₀
    refine h.congr_deriv ?_
    norm_num
    ring
  have hv : HasDerivAt (fun t : ℝ => v₄ * t ^ 4 + v₃ * t ^ 3 + v₂ * t ^ 2 + v₁ * t + v₀)
      (4 * v₄ * y ^ 3 + 3 * v₃ * y ^ 2 + 2 * v₂ * y + v₁) y := by
    have h := (((((hasDerivAt_pow 4 y).const_mul v₄).add
      ((hasDerivAt_pow 3 y).const_mul v₃)).add
      ((hasDerivAt_pow 2 y).const_mul v₂)).add ((hasDerivAt_id' y).const_mul v₁)).add_const v₀
    refine h.congr_deriv ?_
    norm_num
    ring
  have hw : HasDerivAt (fun t : ℝ => w₃ * t ^ 3 + w₂ * t ^ 2 + w₁ * t + w₀)
      (3 * w₃ * y ^ 2 + 2 * w₂ * y + w₁) y := by
    have h := ((((hasDerivAt_pow 3 y).const_mul w₃).add
      ((hasDerivAt_pow 2 y).const_mul w₂)).add ((hasDerivAt_id' y).const_mul w₁)).add_const w₀
    refine h.congr_deriv ?_
    norm_num
    ring
  exact (((he2.mul hu).sub (he1.mul hv)).sub hw).congr_deriv (by ring)
private lemma step8 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 256 512 (-512) 2560 1 32 352 1600 2504 0 0 0 0 y := by
  have : (1 + y + y ^ 2 / 2) * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560)
      ≤ exp y * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560) := by
    grw [quad_le_exp hy]
    nlinarith [sq_nonneg (y - 1), pow_nonneg hy 3, sq_nonneg y]
  have : (0 : ℝ) ≤ 56 + 448 * y + 928 * y ^ 2 + 480 * y ^ 3 + 511 * y ^ 4 + 128 * y ^ 5 := by
    nlinarith [pow_nonneg hy 5, pow_nonneg hy 4, pow_nonneg hy 3, sq_nonneg y, hy]
  have h3 : (0 : ℝ) ≤ exp y * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560)
      - (2504 + 1600 * y + 352 * y ^ 2 + 32 * y ^ 3 + 1 * y ^ 4) := by nlinarith
  calc
    _ ≤ _ := mul_nonneg (exp_pos y).le h3
    _ = _ := by
        simp only [Sf, two_mul, exp_add]
        ring
private lemma step7 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 128 64 (-320) 1440 1 28 268 1064 1440 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 256 512 (-512) 2560 1 32 352 1600 2504 0 0 0 0)
    (fun z => ?_) ?_ step8 hy
  · exact (hasDerivAt_Sf 128 64 (-320) 1440 1 28 268 1064 1440 0 0 0 0 z).congr_deriv
      (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step6 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 64 (-64) (-96) 768 1 24 196 672 768 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 128 64 (-320) 1440 1 28 268 1064 1440 0 0 0 0)
    (fun z => ?_) ?_ step7 hy
  · exact (hasDerivAt_Sf 64 (-64) (-96) 768 1 24 196 672 768 0 0 0 0 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step5 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 32 (-80) 32 368 1 20 136 400 368 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 64 (-64) (-96) 768 1 24 196 672 768 0 0 0 0)
    (fun z => ?_) ?_ step6 hy
  · exact (hasDerivAt_Sf 32 (-80) 32 368 1 20 136 400 368 0 0 0 0 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step4 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 16 (-64) 80 144 1 16 88 224 144 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 32 (-80) 32 368 1 20 136 400 368 0 0 0 0)
    (fun z => ?_) ?_ step5 hy
  · exact (hasDerivAt_Sf 16 (-64) 80 144 1 16 88 224 144 0 0 0 0 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step3 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 8 (-44) 84 30 1 12 52 120 24 0 0 0 6 y := by
  refine nonneg_of_deriv (g := Sf 16 (-64) 80 144 1 16 88 224 144 0 0 0 0)
    (fun z => ?_) ?_ step4 hy
  · exact (hasDerivAt_Sf 8 (-44) 84 30 1 12 52 120 24 0 0 0 6 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step2 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 4 (-28) 70 (-20) 1 8 28 64 (-40) 0 0 6 20 y := by
  refine nonneg_of_deriv (g := Sf 8 (-44) 84 30 1 12 52 120 24 0 0 0 6)
    (fun z => ?_) ?_ step3 hy
  · exact (hasDerivAt_Sf 4 (-28) 70 (-20) 1 8 28 64 (-40) 0 0 6 20 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step1 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 2 (-17) 52 (-36) 1 4 16 32 (-72) 0 3 20 36 y := by
  refine nonneg_of_deriv (g := Sf 4 (-28) 70 (-20) 1 8 28 64 (-40) 0 0 6 20)
    (fun z => ?_) ?_ step2 hy
  · exact (hasDerivAt_Sf 2 (-17) 52 (-36) 1 4 16 32 (-72) 0 3 20 36 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step0 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 1 (-10) 36 (-36) 1 0 16 0 (-72) 1 10 36 36 y := by
  refine nonneg_of_deriv (g := Sf 2 (-17) 52 (-36) 1 4 16 32 (-72) 0 3 20 36)
    (fun z => ?_) ?_ step1 hy
  · exact (hasDerivAt_Sf 1 (-10) 36 (-36) 1 0 16 0 (-72) 1 10 36 36 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma Sf_eq (h : ℝ) :
    Sf 1 (-10) 36 (-36) 1 0 16 0 (-72) 1 10 36 36 (2 * h)
    = 16 * exp h ^ 2 * (h ^ 4 * sinh h ^ 2 - (h ^ 2 + 9) * (h * cosh h - sinh h) ^ 2) := by
  have : exp h ≠ 0 := (exp_pos h).ne'
  have e4 : exp (2 * (2 * h)) = exp h ^ 4 := by simp [←exp_nat_mul]; ring
  have e2 : exp (2 * h) = exp h ^ 2 := by simp [←exp_nat_mul]
  simp only [Sf, sinh_eq, cosh_eq, e4, e2, exp_neg]
  field_simp
  ring
end Sendov
end

set_option autoImplicit false
open Sendov
open Real Set Filter
namespace Sendov
theorem _root_.solution {h : ℝ} (hh : 0 ≤ h) :
    (h ^ 2 + 9) * (h * cosh h - sinh h) ^ 2 ≤ h ^ 4 * sinh h ^ 2 := by
  have h0 := step0 (2 * h) (by linarith)
  rw [Sf_eq] at h0
  have : (0 : ℝ) < 16 * exp h ^ 2 := by positivity
  nlinarith
end Sendov
