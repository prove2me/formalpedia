-- Prove2me | solution 1 for Rudin.ch08_bessel_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T05:26:52.181384+00:00
-- url     : https://prove2.me/submissions/8c596d20-84de-4eba-80d5-a17627873008

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace RudinFix8

open Filter Topology MeasureTheory Rudin

variable {a b : ℝ}

/-- `IntervalIntegrable` on `[a,b]` with `a ≤ b` is integrability for the restricted measure. -/
theorem toInt (hab : a ≤ b) {g : ℝ → ℂ} (h : IntervalIntegrable g volume a b) :
    Integrable g (volume.restrict (Set.Ioc a b)) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 h

theorem toIntR (hab : a ≤ b) {g : ℝ → ℝ} (h : IntervalIntegrable g volume a b) :
    Integrable g (volume.restrict (Set.Ioc a b)) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 h

theorem toL2 (hab : a ≤ b) {g : ℝ → ℂ} (h : IntervalIntegrable g volume a b)
    (h2 : IntervalIntegrable (fun x => ‖g x‖ ^ 2) volume a b) :
    MemLp g 2 (volume.restrict (Set.Ioc a b)) :=
  (memLp_two_iff_integrable_sq_norm (toInt hab h).1).2 (toIntR hab h2)

/-- Pointwise expansion of a squared distance in `ℂ`. -/
theorem norm_sub_sq (z w : ℂ) :
    ‖z - w‖ ^ 2 = ‖z‖ ^ 2 - 2 * (z * (starRingEnd ℂ) w).re + ‖w‖ ^ 2 := by
  have h : ∀ u : ℂ, ‖u‖ ^ 2 = u.re * u.re + u.im * u.im := fun u => RCLike.norm_sq_eq_def
  rw [h, h, h]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring


theorem norm_sq_eq_mul_conj_re (z : ℂ) : ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
  have h : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := RCLike.norm_sq_eq_def
  rw [h]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-! ### The master identity -/

theorem bessel_key (a b : ℝ) (hab : a ≤ b) (φ : ℕ → ℝ → ℂ)
    (hφ : IsOrthonormalSystem φ a b)
    (hφint : ∀ m, IntervalIntegrable (φ m) volume a b)
    (hφ2 : ∀ m, IntervalIntegrable (fun x => ‖φ m x‖ ^ 2) volume a b)
    (f : ℝ → ℂ) (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) volume a b)
    (n : ℕ) (c : ℕ → ℂ) :
    (∫ x in a..b, ‖f x - ∑ m ∈ Finset.range n, c m * φ m x‖ ^ 2)
      = (∫ x in a..b, ‖f x‖ ^ 2)
        - ∑ m ∈ Finset.range n, ‖genFourierCoeff f φ a b m‖ ^ 2
        + ∑ m ∈ Finset.range n, ‖c m - genFourierCoeff f φ a b m‖ ^ 2 := by
  set μ : Measure ℝ := volume.restrict (Set.Ioc a b) with hμ
  have hint : ∀ g : ℝ → ℝ, (∫ x in a..b, g x) = ∫ x, g x ∂μ :=
    fun g => intervalIntegral.integral_of_le hab
  have hintC : ∀ g : ℝ → ℂ, (∫ x in a..b, g x) = ∫ x, g x ∂μ :=
    fun g => intervalIntegral.integral_of_le hab
  have hfL : MemLp f 2 μ := toL2 hab hf hf2
  have hφL : ∀ m, MemLp (φ m) 2 μ := fun m => toL2 hab (hφint m) (hφ2 m)
  have conjL : ∀ u : ℝ → ℂ, MemLp u 2 μ → MemLp (fun x => (starRingEnd ℂ) (u x)) 2 μ := by
    intro u hu
    refine hu.of_le (Complex.continuous_conj.comp_aestronglyMeasurable hu.1) ?_
    filter_upwards with x
    simp
  set S : ℝ → ℂ := fun x => ∑ m ∈ Finset.range n, c m * φ m x with hS
  have hSL : MemLp S 2 μ := memLp_finsetSum _ (fun m _ => (hφL m).const_mul (c m))
  have hprod : ∀ u v : ℝ → ℂ, MemLp u 2 μ → MemLp v 2 μ →
      Integrable (fun x => u x * (starRingEnd ℂ) (v x)) μ :=
    fun u v hu hv => hu.integrable_mul (conjL v hv)
  -- linearity in the conjugated slot
  have L2lin : ∀ u : ℝ → ℂ, MemLp u 2 μ →
      (∫ x, u x * (starRingEnd ℂ) (S x) ∂μ)
        = ∑ m ∈ Finset.range n,
            (starRingEnd ℂ) (c m) * ∫ x, u x * (starRingEnd ℂ) (φ m x) ∂μ := by
    intro u hu
    have hpt : ∀ x, u x * (starRingEnd ℂ) (S x)
        = ∑ m ∈ Finset.range n, (starRingEnd ℂ) (c m) * (u x * (starRingEnd ℂ) (φ m x)) := by
      intro x
      rw [hS]
      simp only [map_sum, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    simp only [hpt]
    rw [integral_finsetSum _ (fun m _ => (hprod u (φ m) hu (hφL m)).const_mul _)]
    exact Finset.sum_congr rfl fun m _ => integral_const_mul _ _
  -- linearity in the plain slot
  have L1lin : ∀ u : ℝ → ℂ, MemLp u 2 μ →
      (∫ x, S x * (starRingEnd ℂ) (u x) ∂μ)
        = ∑ m ∈ Finset.range n, c m * ∫ x, φ m x * (starRingEnd ℂ) (u x) ∂μ := by
    intro u hu
    have hpt : ∀ x, S x * (starRingEnd ℂ) (u x)
        = ∑ m ∈ Finset.range n, c m * (φ m x * (starRingEnd ℂ) (u x)) := by
      intro x
      rw [hS, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    simp only [hpt]
    rw [integral_finsetSum _ (fun m _ => (hprod (φ m) u (hφL m) hu).const_mul _)]
    exact Finset.sum_congr rfl fun m _ => integral_const_mul _ _
  -- orthonormality restated for `μ`
  have horth : ∀ m k, m ≠ k → (∫ x, φ m x * (starRingEnd ℂ) (φ k x) ∂μ) = 0 := by
    intro m k h
    have h1 := hφ.1 k m (Ne.symm h)
    rwa [hintC] at h1
  have hdiag : ∀ m, (∫ x, φ m x * (starRingEnd ℂ) (φ m x) ∂μ) = 1 := by
    intro m
    have h1 : ∀ x, φ m x * (starRingEnd ℂ) (φ m x) = ((‖φ m x‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      simpa using RCLike.mul_conj (K := ℂ) (φ m x)
    simp only [h1]
    rw [integral_complex_ofReal, ← hint, hφ.2 m]
    norm_num
  have hcm : ∀ m, genFourierCoeff f φ a b m = ∫ x, f x * (starRingEnd ℂ) (φ m x) ∂μ := by
    intro m
    rw [genFourierCoeff, hintC]
  have hfS : (∫ x, f x * (starRingEnd ℂ) (S x) ∂μ)
      = ∑ m ∈ Finset.range n, (starRingEnd ℂ) (c m) * genFourierCoeff f φ a b m := by
    rw [L2lin f hfL]
    exact Finset.sum_congr rfl fun m _ => by rw [hcm]
  have hφS : ∀ m ∈ Finset.range n,
      (∫ x, φ m x * (starRingEnd ℂ) (S x) ∂μ) = (starRingEnd ℂ) (c m) := by
    intro m hm
    rw [L2lin (φ m) (hφL m), Finset.sum_eq_single m]
    · rw [hdiag m, mul_one]
    · intro k _ hk
      rw [horth m k (Ne.symm hk), mul_zero]
    · intro h
      exact absurd hm h
  have hSS : (∫ x, S x * (starRingEnd ℂ) (S x) ∂μ)
      = ∑ m ∈ Finset.range n, c m * (starRingEnd ℂ) (c m) := by
    rw [L1lin S hSL]
    exact Finset.sum_congr rfl fun m hm => by rw [hφS m hm]
  -- expand the square
  have hnormS : ∀ x, ‖S x‖ ^ 2 = (S x * (starRingEnd ℂ) (S x)).re := fun x =>
    norm_sq_eq_mul_conj_re (S x)
  have hIf2 : Integrable (fun x => ‖f x‖ ^ 2) μ := toIntR hab hf2
  have hIS2 : Integrable (fun x => ‖S x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hSL.1).1 hSL
  have hIcross : Integrable (fun x => (f x * (starRingEnd ℂ) (S x)).re) μ :=
    (hprod f S hfL hSL).re
  have hexp : (∫ x in a..b, ‖f x - S x‖ ^ 2)
      = (∫ x in a..b, ‖f x‖ ^ 2)
        - 2 * (∫ x, f x * (starRingEnd ℂ) (S x) ∂μ).re
        + (∫ x, S x * (starRingEnd ℂ) (S x) ∂μ).re := by
    rw [hint, hint]
    have hpt : ∀ x, ‖f x - S x‖ ^ 2
        = ‖f x‖ ^ 2 - 2 * (f x * (starRingEnd ℂ) (S x)).re
          + (S x * (starRingEnd ℂ) (S x)).re := by
      intro x
      rw [norm_sub_sq, hnormS]
    have hIS2' : Integrable (fun x => (S x * (starRingEnd ℂ) (S x)).re) μ := by
      have he : (fun x => (S x * (starRingEnd ℂ) (S x)).re) = fun x => ‖S x‖ ^ 2 := by
        funext x; rw [hnormS]
      rw [he]; exact hIS2
    have hIc2 : Integrable (fun x => 2 * (f x * (starRingEnd ℂ) (S x)).re) μ :=
      hIcross.const_mul 2
    have hAB : Integrable
        (fun x => ‖f x‖ ^ 2 - 2 * (f x * (starRingEnd ℂ) (S x)).re) μ := hIf2.sub hIc2
    have hr1 : (∫ x, (f x * (starRingEnd ℂ) (S x)).re ∂μ)
        = (∫ x, f x * (starRingEnd ℂ) (S x) ∂μ).re := by
      simpa using integral_re (𝕜 := ℂ) (hprod f S hfL hSL)
    have hr2 : (∫ x, (S x * (starRingEnd ℂ) (S x)).re ∂μ)
        = (∫ x, S x * (starRingEnd ℂ) (S x) ∂μ).re := by
      simpa using integral_re (𝕜 := ℂ) (hprod S S hSL hSL)
    simp only [hpt]
    rw [integral_add hAB hIS2', integral_sub hIf2 hIc2, integral_const_mul, hr1, hr2]
  rw [hexp, hfS, hSS]
  -- pure algebra on the coefficients
  have halg : ∀ m ∈ Finset.range n,
      ‖c m - genFourierCoeff f φ a b m‖ ^ 2
        = ‖c m‖ ^ 2 - 2 * ((starRingEnd ℂ) (c m) * genFourierCoeff f φ a b m).re
          + ‖genFourierCoeff f φ a b m‖ ^ 2 := by
    intro m _
    rw [norm_sub_sq]
    congr 2
    have : ((starRingEnd ℂ) (c m) * genFourierCoeff f φ a b m)
        = (starRingEnd ℂ) (c m * (starRingEnd ℂ) (genFourierCoeff f φ a b m)) := by
      simp [mul_comm]
    rw [this, Complex.conj_re]
  rw [Finset.sum_congr rfl halg]
  have hre1 : (∑ m ∈ Finset.range n, (starRingEnd ℂ) (c m) * genFourierCoeff f φ a b m).re
      = ∑ m ∈ Finset.range n, ((starRingEnd ℂ) (c m) * genFourierCoeff f φ a b m).re := by
    simp [Complex.re_sum]
  have hre2 : (∑ m ∈ Finset.range n, c m * (starRingEnd ℂ) (c m)).re
      = ∑ m ∈ Finset.range n, ‖c m‖ ^ 2 := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun m _ => (norm_sq_eq_mul_conj_re (c m)).symm
  rw [hre1, hre2]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring


/-! ### Best approximation and Bessel's inequality -/

theorem bessel (a b : ℝ) (hab : a ≤ b) (φ : ℕ → ℝ → ℂ)
    (hφ : IsOrthonormalSystem φ a b)
    (hφint : ∀ m, IntervalIntegrable (φ m) volume a b)
    (hφ2 : ∀ m, IntervalIntegrable (fun x => ‖φ m x‖ ^ 2) volume a b)
    (f : ℝ → ℂ) (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) volume a b)
    (n : ℕ) (γ : ℕ → ℂ) :
    (∫ x in a..b, ‖f x - ∑ m ∈ Finset.range n, genFourierCoeff f φ a b m * φ m x‖ ^ 2) ≤
      (∫ x in a..b, ‖f x - ∑ m ∈ Finset.range n, γ m * φ m x‖ ^ 2) ∧
    (∑ m ∈ Finset.range n, ‖genFourierCoeff f φ a b m‖ ^ 2) ≤ ∫ x in a..b, ‖f x‖ ^ 2 := by
  have hc := bessel_key a b hab φ hφ hφint hφ2 f hf hf2 n (genFourierCoeff f φ a b)
  have hg := bessel_key a b hab φ hφ hφint hφ2 f hf hf2 n γ
  have hzero : ∑ m ∈ Finset.range n,
      ‖genFourierCoeff f φ a b m - genFourierCoeff f φ a b m‖ ^ 2 = 0 := by
    simp
  rw [hzero, add_zero] at hc
  have hCnn : 0 ≤ ∑ m ∈ Finset.range n, ‖γ m - genFourierCoeff f φ a b m‖ ^ 2 :=
    Finset.sum_nonneg fun m _ => by positivity
  have hnn : 0 ≤ ∫ x in a..b,
      ‖f x - ∑ m ∈ Finset.range n, genFourierCoeff f φ a b m * φ m x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun x _ => by positivity
  constructor
  · rw [hc, hg]
    linarith
  · rw [hc] at hnn
    linarith

end RudinFix8

open Filter Topology Rudin in
theorem solution (a b : ℝ) (hab : a ≤ b) (φ : ℕ → ℝ → ℂ)
    (hφ : IsOrthonormalSystem φ a b)
    (hφint : ∀ m, IntervalIntegrable (φ m) MeasureTheory.volume a b)
    (hφ2 : ∀ m, IntervalIntegrable (fun x => ‖φ m x‖ ^ 2) MeasureTheory.volume a b)
    (f : ℝ → ℂ) (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume a b)
    (n : ℕ) (γ : ℕ → ℂ) :
    (∫ x in a..b, ‖f x - ∑ m ∈ Finset.range n, genFourierCoeff f φ a b m * φ m x‖ ^ 2) ≤
      (∫ x in a..b, ‖f x - ∑ m ∈ Finset.range n, γ m * φ m x‖ ^ 2) ∧
    (∑ m ∈ Finset.range n, ‖genFourierCoeff f φ a b m‖ ^ 2) ≤ ∫ x in a..b, ‖f x‖ ^ 2 :=
  RudinFix8.bessel a b hab φ hφ hφint hφ2 f hf hf2 n γ
