-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetentionMeasure_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/fd469f0a-a597-46e9-a87a-30a5aa8f0aa6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (dimension : ℕ) :
    MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) := by
  unfold hammingRetentionMeasure
  infer_instance
end TwoDegenerateGraphs
