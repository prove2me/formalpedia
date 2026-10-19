-- Prove2me | solution 1 for TwoDegenerateGraphs.manuscriptHammingRadius_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/6a8d8952-4b63-42d1-bb91-21c332d1fef6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution (dimension : ℕ) :
    (manuscriptHammingRadius dimension : ℝ) ≤
      tau * (dimension : ℝ) := by
  unfold manuscriptHammingRadius
  exact Nat.floor_le
    (mul_nonneg tau_pos.le (Nat.cast_nonneg dimension))
end TwoDegenerateGraphs
