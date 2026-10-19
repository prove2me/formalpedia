-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetentionMeasure_integral_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/30d99f4e-34f9-4fd0-8dfa-cd76428ed7b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_integrable

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    (∫ retained,
      observable retained ∂hammingRetentionMeasure dimension) =
      ∑ retained : Set (Bool × HammingWord dimension),
        (hammingRetentionMeasure dimension).real {retained} *
          observable retained := by
  classical
  simpa [smul_eq_mul] using
    (MeasureTheory.integral_fintype
      (hammingRetentionMeasure_integrable dimension observable))
end TwoDegenerateGraphs
