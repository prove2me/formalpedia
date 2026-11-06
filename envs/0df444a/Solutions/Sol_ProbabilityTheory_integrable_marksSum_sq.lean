-- Prove2me | solution 1 for ProbabilityTheory.integrable_marksSum_sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:02:26.73262+00:00
-- url     : https://prove2.me/submissions/2a8f6abf-5d58-4e5d-9285-160208a83bf0

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Theorems.Thm_ProbabilityTheory_integrable_prmPieceLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution
    {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {k : ℕ} [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ)
    {f : E → ℝ} (hf : Measurable f)
    (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k)))
    (j : ℕ) :
    Integrable (fun ω => (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2) μ := by
  classical
  have hInt_f : ∀ n, Integrable (fun ω => f (X k n ω)) μ := by
    intro n
    have hI : Integrable f (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]
      exact ProbabilityTheory.integrable_prmPieceLaw hf hfi
    exact hI.comp_measurable (hd.measurable_point k n)
  have hInt_f2 : ∀ n, Integrable (fun ω => f (X k n ω) ^ 2) μ := by
    intro n
    have hI : Integrable (fun x => f x ^ 2) (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]
      exact ProbabilityTheory.integrable_prmPieceLaw (hf.pow_const 2) hfi2
    exact hI.comp_measurable (hd.measurable_point k n)
  have hprod : ∀ n n', Integrable (fun ω => f (X k n ω) * f (X k n' ω)) μ := by
    intro n n'
    by_cases h : n = n'
    · subst h
      simpa [pow_two] using hInt_f2 n
    · exact (((hd.iIndepFun_point_piece k).indepFun h).comp hf hf).integrable_mul
        (hInt_f n) (hInt_f n')
  have hexp : (fun ω => (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2) =
      fun ω => ∑ n ∈ Finset.range j, ∑ n' ∈ Finset.range j,
        f (X k n ω) * f (X k n' ω) := by
    funext ω
    rw [pow_two, Finset.sum_mul_sum]
  rw [hexp]
  exact integrable_finsetSum _ fun n _ =>
    integrable_finsetSum _ fun n' _ => hprod n n'
