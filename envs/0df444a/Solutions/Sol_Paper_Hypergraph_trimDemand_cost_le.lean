-- Prove2me | solution 1 for Paper.Hypergraph.trimDemand_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:24.478987+00:00
-- url     : https://prove2.me/submissions/af1392cc-acf9-4f21-a028-b3fdf6b2b254

import Definitions.Def_Paper_RoundingAveraging
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Paper_RoundingIndependence
import Theorems.Thm_Paper_Hypergraph_coverCost_mono
import Theorems.Thm_Paper_Hypergraph_coverCost_smul


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ} (hx : H.UnitDemand x) (ε : ℝ) :
    H.coverCost (trimDemand x ε) ≤ 2 * H.coverCost x := by
  rw [← H.coverCost_smul x (by norm_num : (0 : ℝ) < 2)]
  apply H.coverCost_mono
  intro v hv
  change trimDemand x ε v ≤ 2 * x v
  dsimp [trimDemand]
  split_ifs
  · exact min_le_left _ _
  · linarith [(hx v hv).1]
end Paper.Hypergraph
