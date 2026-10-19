-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetentionMeasure_real_deviation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/94b4bdbc-3db0-408a-9730-65a0a957c9a2

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_isProbability
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_memLp_two

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ)
    (threshold : ℝ) (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |observable retained -
            (∫ candidate,
              observable candidate ∂hammingRetentionMeasure dimension)|} ≤
      ProbabilityTheory.variance observable
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  have hchebyshev :=
    ProbabilityTheory.meas_ge_le_variance_div_sq
      (hammingRetentionMeasure_memLp_two dimension observable)
      hthreshold
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hchebyshev
  have hnonnegative :
      0 ≤ ProbabilityTheory.variance observable
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := by
    exact div_nonneg
      (ProbabilityTheory.variance_nonneg observable
        (hammingRetentionMeasure dimension))
      (sq_nonneg threshold)
  simpa [MeasureTheory.Measure.real, ENNReal.toReal_ofReal hnonnegative]
    using hreal
end TwoDegenerateGraphs
