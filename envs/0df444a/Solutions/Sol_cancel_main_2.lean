-- Prove2me | solution 2 for cancel_main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:52:38.237336+00:00
-- url     : https://prove2.me/submissions/62ea6fbd-d253-4eb1-8e96-8208a0a9afd9

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
import Theorems.Thm_cumsum_succ
import Theorems.Thm_P2M_cancel_aux__0fa0ad8380d6
import Theorems.Thm_P2M_W21_hf__c0784783506d
import Theorems.Thm_W21_hf


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
theorem _root_.solution {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) (hn : 2 ≤ n) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  change (∑ i ∈ Finset.range n, f i * g i) ≤ C * cumsum g n
  refine (cancel_aux' hf hg hf' hg' n).trans_eq ?_
  have hindex : n - 1 - 1 + 1 = n - 1 := by omega
  have hcast : (n : ℝ) = ↑(n - 1) + 1 := by
    exact_mod_cast (show n = (n - 1) + 1 by omega)
  have hcast' : (↑(n - 1 - 1) : ℝ) + 1 = ↑(n - 1) := by
    exact_mod_cast hindex
  have hsum : cumsum g n = cumsum g (n - 1) + g (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    exact cumsum_succ (n - 1)
  rw [hindex, hcast', hcast, hsum]
  ring
