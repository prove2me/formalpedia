-- Prove2me | solution 2 for comp_exp_support
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:49:51.406779+00:00
-- url     : https://prove2.me/submissions/3935ab58-91d2-48d3-83c8-1678bae8e076

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

theorem solution {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  have hK : IsCompact (tsupport Ψ) := hsupp
  have hsub : tsupport Ψ ⊆ Ioi 0 := hplus
  have himg : IsCompact (Real.log '' tsupport Ψ) :=
    hK.image_of_continuousOn (Real.continuousOn_log.mono (fun y hy => ne_of_gt (hsub hy)))
  refine himg.of_isClosed_subset (isClosed_tsupport _) ?_
  intro y hy
  refine ⟨Real.exp y, ?_, Real.log_exp y⟩
  have : tsupport (Ψ ∘ rexp) ⊆ rexp ⁻¹' tsupport Ψ := by
    refine closure_minimal ?_ (isClosed_tsupport Ψ |>.preimage Real.continuous_exp)
    intro z hz
    exact subset_closure hz
  exact this hy
