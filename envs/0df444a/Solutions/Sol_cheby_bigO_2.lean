-- Prove2me | solution 2 for cheby.bigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:48:32.015911+00:00
-- url     : https://prove2.me/submissions/409782ea-f091-40db-bd80-50369917c53b

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
import Theorems.Thm_continuous_multiplicative_ofAdd
import Theorems.Thm_continuous_FourierIntegral
import Theorems.Thm_cumsum_zero
import Theorems.Thm_nabla_cumsum
import Theorems.Thm_cumsum_nonneg
import Theorems.Thm_nabla_mul
import Theorems.Thm_nnabla_mul
import Theorems.Thm_F_add
import Theorems.Thm_F_mul
import Theorems.Thm_F_neg
import Theorems.Thm_F_sub
import Theorems.Thm_OAI_QRH_b83dbbd_deriv_ofReal
import Theorems.Thm_W21_norm_nonneg
attribute [local simp] F_add
attribute [local simp] F_mul
attribute [local simp] F_neg
attribute [local simp] F_sub
attribute [local simp] OAI.QRH_b83dbbd.deriv_ofReal


attribute [local continuity] continuous_multiplicative_ofAdd
attribute [local continuity] continuous_FourierIntegral
attribute [local fun_prop] continuous_FourierIntegral
attribute [local simp] cumsum_zero
attribute [local simp] nabla_cumsum
attribute [local simp] nabla_mul
attribute [local simp] nnabla_mul

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
namespace cheby
theorem _root_.solution (h : (∃ C : ℝ, ∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖(f k : ℂ)‖) n ≤ C * n)) :
    cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  have l1 : 0 ≤ cumsum (‖f ·‖) := cumsum_nonneg (fun _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := h
  apply isBigO_of_le' (c := C) atTop
  intro n
  rw [Real.norm_eq_abs, abs_eq_self.mpr (l1 n)]
  simpa using hC n
end cheby
