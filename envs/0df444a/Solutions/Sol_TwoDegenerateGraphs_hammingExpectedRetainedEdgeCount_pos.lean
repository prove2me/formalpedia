-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingExpectedRetainedEdgeCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/f02e3f2b-c1db-4157-8f10-b41840ce9b94

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedEdgeCount_eq

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ) :
    0 < hammingExpectedRetainedEdgeCount dimension radius := by
  have hterm :
      1 ≤ ∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance := by
    have hzero := Finset.single_le_sum
      (s := Finset.range (radius + 1))
      (f := fun distance : ℕ => dimension.choose distance)
      (fun distance _ => Nat.zero_le _)
      (show 0 ∈ Finset.range (radius + 1) by simp)
    simpa using hzero
  have hdegree :
      0 < ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < ∑ distance ∈ Finset.range (radius + 1),
      dimension.choose distance by omega)
  rw [hammingExpectedRetainedEdgeCount_eq]
  have hprobability := hammingRetentionProbability_pos dimension
  positivity
end TwoDegenerateGraphs
