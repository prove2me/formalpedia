-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetentionMeasure_memLp_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/196cb445-bf44-41a8-aedd-a8d5014d6263

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
    MeasureTheory.MemLp observable 2
      (hammingRetentionMeasure dimension) := by
  apply (MeasureTheory.memLp_two_iff_integrable_sq
    (hammingRetentionMeasure_integrable dimension observable).aestronglyMeasurable).mpr
  exact hammingRetentionMeasure_integrable dimension
    (fun retained => observable retained ^ 2)
end TwoDegenerateGraphs
