-- Prove2me | solution 1 for P2M_bound_I1__14f9a305b1fb
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:34:55.791528+00:00
-- url     : https://prove2.me/submissions/5a05d9ea-fb5a-4320-91b5-51d0f977985c

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Lemmas
import Definitions.Def_PrimeNumberTheoremAnd_Fourier
import Definitions.Def_PrimeNumberTheoremAnd_SmoothExistence
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Definitions.Def_PrimeNumberTheoremAnd_Wiener
import Theorems.Thm_summable_fourier_aux
import Theorems.Thm_limiting_fourier_lim1_aux
import Theorems.Thm_W21_norm_nonneg
import Theorems.Thm_P2M_bound_sum_log__1352fedcd6c1
set_option autoImplicit true
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate
variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]
attribute [fun_prop] Real.continuous_fourierChar
attribute [fun_prop] measurable_coe_nnreal_ennreal

theorem solution {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21)
    (hcheby : (∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖(f k : ℂ)‖) n ≤ C * n)) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
      W21.norm ψ * C * (1 + 2 * π ^ 2) := by
  have hx0 : 0 < x := by linarith
  have l5 : Summable fun i ↦ ‖f i‖ / (i : ℝ) *
      ((1 + (1 / (2 * π) * Real.log ((i : ℝ) / x)) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux (f := f) (x := x)
      ⟨C, hcheby⟩ hx0 1 (zero_le_one' ℝ)
  have l6 (i : ℕ) :
      ‖f i / (i : ℂ) * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
        W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * Real.log (i / x)) ^ 2)⁻¹) :=
    summable_fourier_aux (f := f) (x := x) ψ i
  have l1 : Summable fun i ↦
      ‖f i / (i : ℂ) * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log ((i : ℝ) / x))‖ := by
    exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) l6
      (by simpa using l5.mul_left (W21.norm ψ))
  calc
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
        ∑' i, ‖f i / (i : ℂ) * 𝓕 (ψ : ℝ → ℂ)
          (1 / (2 * π) * Real.log ((i : ℝ) / x))‖ := norm_tsum_le_tsum_norm l1
    _ ≤ W21.norm ψ * ∑' i, ‖f i‖ / i *
        (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by
      rw [← tsum_mul_left]
      exact Summable.tsum_mono l1 (l5.mul_left (W21.norm ψ)) l6
    _ ≤ W21.norm ψ * (C * (1 + 2 * π ^ 2)) :=
      mul_le_mul_of_nonneg_left (bound_sum_log' hcheby hx) W21.norm_nonneg
    _ = W21.norm ψ * C * (1 + 2 * π ^ 2) := by ring
