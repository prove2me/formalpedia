-- Prove2me | solution 1 for ProbabilityTheory.setIntegral_sq_pieceSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:25:02.063353+00:00
-- url     : https://prove2.me/submissions/c06a568f-2558-44e2-9880-19ee23f39a53

import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Theorems.Thm_ProbabilityTheory_setIntegral_count_marksFun
import Theorems.Thm_ProbabilityTheory_integral_marksSum_sq_eq
import Theorems.Thm_ProbabilityTheory_measureReal_count_eq

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
    (hd : IsPoissonPointFamily K X m μ) {f : E → ℝ}
    (hf : Measurable f)
    (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k)))
    (j : ℕ) :
    ∫ x in {ω | K k ω = j}, (pieceSum K X f k x) ^ 2 ∂μ =
      (poissonMeasure (m (prmPiece m k)).toNNReal).real {j} *
      ((j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k)) +
       (j : ℝ) * ((j : ℝ) - 1) *
       (∫ x, f x ∂(prmPieceLaw m k)) ^ 2) := by
  have hψmeas : Measurable (fun y : ℕ → E =>
      (∑ n ∈ Finset.range j, f (y n)) ^ 2) :=
    (Finset.measurable_sum _ fun n _ => hf.comp (measurable_pi_apply n)).pow_const 2
  calc ∫ x in {ω | K k ω = j}, (pieceSum K X f k x) ^ 2 ∂μ
      = ∫ x in {ω | K k ω = j},
          (fun y : ℕ → E => (∑ n ∈ Finset.range j, f (y n)) ^ 2)
            (fun n => X k n x) ∂μ := by
        refine setIntegral_congr_fun
          (hd.measurable_count k (measurableSet_singleton j)) ?_
        intro ω hω
        show (pieceSum K X f k ω) ^ 2 = _
        rw [pieceSum, show K k ω = j from hω]
    _ = μ.real {ω | K k ω = j} *
          ∫ x, (fun y : ℕ → E => (∑ n ∈ Finset.range j, f (y n)) ^ 2)
            (fun n => X k n x) ∂μ :=
        ProbabilityTheory.setIntegral_count_marksFun hd j hψmeas
    _ = (poissonMeasure (m (prmPiece m k)).toNNReal).real {j} *
          ((j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k)) +
           (j : ℝ) * ((j : ℝ) - 1) *
           (∫ x, f x ∂(prmPieceLaw m k)) ^ 2) := by
        rw [ProbabilityTheory.measureReal_count_eq hd j]
        congr 1
        exact ProbabilityTheory.integral_marksSum_sq_eq hd hf hfi hfi2 j
