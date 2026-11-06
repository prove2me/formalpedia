-- Prove2me | solution 1 for continuous_LSeries_aux
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:31:54.007299+00:00
-- url     : https://prove2.me/submissions/e20d9cb2-4f24-4653-9301-5343f7ba3ca0

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

theorem solution (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by
  unfold LSeries
  apply continuous_tsum (u := nterm f σ')
  · intro n
    by_cases hn : n = 0
    · simpa [LSeries.term_def, hn] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
    · simp only [LSeries.term_of_ne_zero hn]
      have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      simp_rw [Complex.cpow_def_of_ne_zero hnc]
      exact continuous_const.div (by fun_prop) (fun x => Complex.exp_ne_zero _)
  · exact hf
  · intro n x
    rw [LSeries.norm_term_eq, nterm]
    simp
