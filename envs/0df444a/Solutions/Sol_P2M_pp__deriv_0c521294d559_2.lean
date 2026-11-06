-- Prove2me | solution 2 for P2M_pp__deriv_0c521294d559
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:49:28.38772+00:00
-- url     : https://prove2.me/submissions/4668a77e-8209-47e2-beec-2fe080584364

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
import Theorems.Thm_BoundedAtFilter_add_const

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
attribute [local gcongr] _root_.norm_lt_norm_of_nonneg
theorem _root_.solution (a x : ℝ) : HasDerivAt (pp' a) (a ^ 2 * 2) x := by
  change HasDerivAt (fun y : ℝ => a ^ 2 * (2 * (y + 1))) (a ^ 2 * 2) x
  convert hasDerivAt_id x |>.add_const 1 |>.const_mul 2 |>.const_mul (a ^ 2)
    using 1 <;> first | rfl | ring
