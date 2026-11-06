-- Prove2me | solution 1 for WeakPNT
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:08:01.695868+00:00
-- url     : https://prove2.me/submissions/bdbe3301-c69d-4581-a2ea-715bd3594b4a

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
import Theorems.Thm_ZetaNine_HarmonicStability_psi_pnt_rate
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
attribute [local instance] _p2m_local_instance_2ee1fa6ce2_1687

theorem solution : Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1) := by
  have hcum (N : ℕ) : cumsum Λ (N + 1) = Chebyshev.psi N := by
    simp only [cumsum, Chebyshev.psi, Nat.floor_natCast]
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Ioc] at hn
      simp only [Finset.mem_range]
      omega
    · intro n hnrange hnIoc
      simp only [Finset.mem_range] at hnrange
      simp only [Finset.mem_Ioc, not_and] at hnIoc
      have hn0 : n = 0 := by omega
      simp [hn0]
  rw [← tendsto_add_atTop_iff_nat 1]
  have hp : Tendsto (fun N : ℕ ↦ Chebyshev.psi (N : ℝ) / (N : ℝ)) atTop (𝓝 1) :=
    ZetaNine.HarmonicStability.psi_pnt_rate.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun N : ℕ ↦ (N : ℝ) / (N + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have hprod : Tendsto
      (fun N : ℕ ↦ (Chebyshev.psi (N : ℝ) / (N : ℝ)) * ((N : ℝ) / (N + 1)))
      atTop (𝓝 1) := by
    simpa using hp.mul hr
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [hcum]
  simp only [Nat.cast_add, Nat.cast_one]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
