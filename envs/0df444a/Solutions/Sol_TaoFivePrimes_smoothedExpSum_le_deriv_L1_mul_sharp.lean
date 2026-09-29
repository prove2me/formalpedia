-- Prove2me | solution 1 for TaoFivePrimes.smoothedExpSum_le_deriv_L1_mul_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:42:27.075263+00:00
-- url     : https://prove2.me/submissions/d4dd397d-f8ff-4199-ad6d-7f2189b0803d

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
open TaoFivePrimes

namespace TaoL42

theorem norm_expCircle (θ : ℝ) : ‖expCircle θ‖ = 1 := by
  unfold expCircle; rw [Complex.norm_exp]; norm_num

theorem cont_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (deriv f) := by
  have := ContDiff.continuous_iteratedDeriv 1 hf (by exact_mod_cast le_top)
  simpa [iteratedDeriv_one] using this

/-- The increment of `η` is controlled by the `L¹` norm of `η'` over the interval. -/
theorem abs_sub_le_integral {eta : ℝ → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta) {u v : ℝ}
    (huv : u ≤ v) : |eta v - eta u| ≤ ∫ t in u..v, |deriv eta t| := by
  have hcd : Continuous (deriv eta) := cont_deriv heta
  have hFTC : ∫ t in u..v, deriv eta t = eta v - eta u :=
    intervalIntegral.integral_deriv_eq_sub (fun t _ => heta.differentiable (by simp) t)
      (hcd.intervalIntegrable _ _)
  rw [← hFTC]
  have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := deriv eta) (a := u) (b := v) huv
  simpa [Real.norm_eq_abs] using h

/-- Telescoping the increments over the sampling points `n/x`. -/
theorem telescope {eta : ℝ → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta) {x : ℝ} (hx : 0 < x) :
    ∀ N : ℕ, (∑ i ∈ Finset.range N,
        ∫ t in ((i:ℝ)/x)..(((i:ℕ)+1 : ℝ)/x), |deriv eta t|)
      = ∫ t in (0:ℝ)..((N:ℝ)/x), |deriv eta t| := by
  have hcd : Continuous (deriv eta) := cont_deriv heta
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      rw [intervalIntegral.integral_add_adjacent_intervals
        ((hcd.abs).intervalIntegrable _ _) ((hcd.abs).intervalIntegrable _ _)]


/-- **Tao, Lemma 4.2.**  A smooth cutoff can be replaced by the sharp truncation
`1_{[0,1]}` at the cost of a factor `‖η'‖_{L¹}`. -/
theorem etail (eta : ℝ → ℝ) (q₀ : ℕ) (x alpha B : ℝ)
    (hx : 1 ≤ x) (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hcs : HasCompactSupport eta)
    (hsupp : ∀ t : ℝ, 1 ≤ t → eta t = 0)
    (hB : ∀ N : ℕ, N ≤ ⌊x⌋₊ →
      ‖∑ n ∈ Finset.range (N+1),
        (if Nat.Coprime n q₀ then (Λ n : ℂ) * expCircle (alpha * n) else 0)‖ ≤ B) :
    ‖smoothedExpSum eta q₀ x alpha‖ ≤ (∫ u : ℝ, |deriv eta u|) * B := by
  classical
  have hx0 : (0:ℝ) < x := by linarith
  have hcd : Continuous (deriv eta) := cont_deriv heta
  have hIabs : Integrable (fun u : ℝ => |deriv eta u|) := by
    have : Integrable (fun u : ℝ => ‖deriv eta u‖) :=
      (hcd.norm).integrable_of_hasCompactSupport (hcs.deriv.norm)
    simpa [Real.norm_eq_abs] using this
  set N : ℕ := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  set a : ℕ → ℂ := fun n => ((eta ((n : ℝ) / x) : ℝ) : ℂ) with ha
  set c : ℕ → ℂ := fun n =>
    (if Nat.Coprime n q₀ then (Λ n : ℂ) * expCircle (alpha * n) else 0) with hcdef
  -- the sum is finite and factors as `a * c`
  have hvanish : ∀ n : ℕ, n ∉ Finset.range (N+1) → eta ((n : ℝ) / x) = 0 := by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    refine hsupp _ (le_of_lt ?_)
    rw [lt_div_iff₀ hx0, one_mul]
    have h1 : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 := Nat.lt_floor_add_one x
    rw [← hN] at h2
    linarith
  have hsum : smoothedExpSum eta q₀ x alpha = ∑ n ∈ Finset.range (N+1), a n * c n := by
    rw [show smoothedExpSum eta q₀ x alpha
        = ∑ n ∈ Finset.range (N+1),
          (if Nat.Coprime n q₀ then
            (Λ n : ℂ) * expCircle (alpha * n) * (eta ((n : ℝ) / x) : ℂ) else 0) from by
      refine tsum_eq_sum ?_
      intro n hn
      by_cases h : Nat.Coprime n q₀
      · rw [if_pos h]; simp [hvanish n hn]
      · rw [if_neg h]]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : Nat.Coprime n q₀
    · rw [if_pos h, ha, hcdef]; simp only [if_pos h]; ring
    · rw [if_neg h, hcdef]; simp only [if_neg h]; ring
  -- summation by parts
  have habel := Finset.sum_range_by_parts a c (N+1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at habel
  rw [hsum, habel]
  -- bound each piece
  have hBnn : (0:ℝ) ≤ B := le_trans (norm_nonneg _) (hB 0 (by omega))
  have hstep : ∀ i : ℕ, ‖a (i+1) - a i‖
      ≤ ∫ t in ((i:ℝ)/x)..(((i:ℕ)+1 : ℝ)/x), |deriv eta t| := by
    intro i
    have hle : ((i:ℝ)/x) ≤ (((i:ℕ)+1 : ℝ)/x) := by
      have h : (i:ℝ) ≤ ((i:ℕ):ℝ) + 1 := by push_cast; linarith
      gcongr
    have heq : ‖a (i+1) - a i‖ = |eta ((((i:ℕ)+1 : ℝ))/x) - eta ((i:ℝ)/x)| := by
      rw [ha]
      simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      push_cast
      ring_nf
    rw [heq]
    exact abs_sub_le_integral heta hle
  have hlast : ‖a N‖ ≤ ∫ t in ((N:ℝ)/x)..(1:ℝ), |deriv eta t| := by
    have hle : ((N:ℝ)/x) ≤ 1 := by
      rw [div_le_one hx0]; exact hNx
    have h0 : eta 1 = 0 := hsupp 1 le_rfl
    have := abs_sub_le_integral heta (u := (N:ℝ)/x) (v := 1) hle
    rw [h0] at this
    rw [ha]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    calc |eta ((N:ℝ)/x)| = |0 - eta ((N:ℝ)/x)| := by rw [zero_sub, abs_neg]
      _ ≤ _ := this
  -- assemble
  have hG : ∀ M : ℕ, M ≤ N → ‖∑ j ∈ Finset.range (M+1), c j‖ ≤ B := by
    intro M hM
    rw [hcdef]
    exact hB M (by omega)
  have hT1 : ‖a N * ∑ i ∈ Finset.range (N+1), c i‖
      ≤ (∫ t in ((N:ℝ)/x)..(1:ℝ), |deriv eta t|) * B := by
    rw [norm_mul]
    have hnn : (0:ℝ) ≤ ‖a N‖ := norm_nonneg _
    have h2 := hG N le_rfl
    calc ‖a N‖ * ‖∑ i ∈ Finset.range (N+1), c i‖ ≤ ‖a N‖ * B :=
          mul_le_mul_of_nonneg_left h2 hnn
      _ ≤ (∫ t in ((N:ℝ)/x)..(1:ℝ), |deriv eta t|) * B :=
          mul_le_mul_of_nonneg_right hlast hBnn
  have hT2 : ‖∑ i ∈ Finset.range N, (a (i+1) - a i) * ∑ j ∈ Finset.range (i+1), c j‖
      ≤ (∫ t in (0:ℝ)..((N:ℝ)/x), |deriv eta t|) * B := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [← telescope heta hx0 N, Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    simp only [Finset.mem_range] at hi
    rw [norm_mul]
    calc ‖a (i+1) - a i‖ * ‖∑ j ∈ Finset.range (i+1), c j‖
        ≤ ‖a (i+1) - a i‖ * B :=
          mul_le_mul_of_nonneg_left (hG i (by omega)) (norm_nonneg _)
      _ ≤ (∫ t in ((i:ℝ)/x)..(((i:ℕ)+1 : ℝ)/x), |deriv eta t|) * B :=
          mul_le_mul_of_nonneg_right (hstep i) hBnn
  have hsplit : (∫ t in (0:ℝ)..((N:ℝ)/x), |deriv eta t|)
      + (∫ t in ((N:ℝ)/x)..(1:ℝ), |deriv eta t|) = ∫ t in (0:ℝ)..(1:ℝ), |deriv eta t| :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hcd.abs).intervalIntegrable _ _) ((hcd.abs).intervalIntegrable _ _)
  have hfull : (∫ t in (0:ℝ)..(1:ℝ), |deriv eta t|) ≤ ∫ u : ℝ, |deriv eta u| := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact MeasureTheory.setIntegral_le_integral hIabs
      (Filter.Eventually.of_forall (fun t => abs_nonneg _))
  calc ‖a N * (∑ i ∈ Finset.range (N+1), c i)
        - ∑ i ∈ Finset.range N, (a (i+1) - a i) * ∑ j ∈ Finset.range (i+1), c j‖
      ≤ ‖a N * ∑ i ∈ Finset.range (N+1), c i‖
        + ‖∑ i ∈ Finset.range N, (a (i+1) - a i) * ∑ j ∈ Finset.range (i+1), c j‖ :=
        norm_sub_le _ _
    _ ≤ (∫ t in ((N:ℝ)/x)..(1:ℝ), |deriv eta t|) * B
        + (∫ t in (0:ℝ)..((N:ℝ)/x), |deriv eta t|) * B := by linarith [hT1, hT2]
    _ = (∫ t in (0:ℝ)..(1:ℝ), |deriv eta t|) * B := by rw [← hsplit]; ring
    _ ≤ (∫ u : ℝ, |deriv eta u|) * B := mul_le_mul_of_nonneg_right hfull hBnn

end TaoL42

theorem solution (eta : ℝ → ℝ) (q₀ : ℕ) (x alpha B : ℝ)
    (hx : 1 ≤ x) (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hcs : HasCompactSupport eta)
    (hsupp : ∀ t : ℝ, 1 ≤ t → eta t = 0)
    (hB : ∀ N : ℕ, N ≤ ⌊x⌋₊ →
      ‖∑ n ∈ Finset.range (N+1),
        (if Nat.Coprime n q₀ then
          (ArithmeticFunction.vonMangoldt n : ℂ) * TaoFivePrimes.expCircle (alpha * n)
         else 0)‖ ≤ B) :
    ‖TaoFivePrimes.smoothedExpSum eta q₀ x alpha‖
      ≤ (∫ u : ℝ, |deriv eta u|) * B :=
  TaoL42.etail eta q₀ x alpha B hx heta hcs hsupp hB
