-- Prove2me | solution 1 for ProbabilityTheory.integral_marksSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:31:42.202047+00:00
-- url     : https://prove2.me/submissions/5e15a40f-ef95-4b70-a22e-b0c333de03cd

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Theorems.Thm_ProbabilityTheory_integrable_prmPieceLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {k : ℕ}
    [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ)
    {g : E → ℝ} (hg : Measurable g)
    (hgi : Integrable g (m.restrict (prmPiece m k))) (j : ℕ) :
    ∫ ω, ∑ n ∈ Finset.range j, g (X k n ω) ∂μ =
      (j : ℝ) * ∫ x, g x ∂(prmPieceLaw m k) := by
  have hterm : ∀ n, Integrable (fun ω => g (X k n ω)) μ := by
    intro n
    have hI : Integrable g (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]
      exact ProbabilityTheory.integrable_prmPieceLaw hg hgi
    exact hI.comp_measurable (hd.measurable_point k n)
  have heach : ∀ n, ∫ ω, g (X k n ω) ∂μ =
      ∫ x, g x ∂(prmPieceLaw m k) := by
    intro n
    rw [← (hd.law_point k n).map_eq,
      integral_map (hd.measurable_point k n).aemeasurable
        hg.aestronglyMeasurable]
  rw [integral_finsetSum _ (fun n _ => hterm n)]
  simp_rw [heach]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
