-- Prove2me | solution 2 for P2M_pp__deriv_eq_cd11c1fa4d26
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:15:21.10622+00:00
-- url     : https://prove2.me/submissions/1e1907a4-ec66-4ba7-84b8-cb6ba524e4c2

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

theorem solution (a : ℝ) : deriv (pp' a) = fun _ => a ^ 2 * 2 := by
  funext x
  have h : HasDerivAt (pp' a) (a ^ 2 * 2) x := by
    change HasDerivAt (fun y : ℝ => a ^ 2 * (2 * (y + 1))) (a ^ 2 * 2) x
    simpa only [id_eq, mul_one] using
      ((((hasDerivAt_id x).add_const (1 : ℝ)).const_mul (2 : ℝ)).const_mul (a ^ 2))
  exact h.deriv
