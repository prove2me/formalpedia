-- Prove2me | solution 1 for TwoDegenerateGraphs.independentBinaryPairMass_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/9379147d-2249-48df-ba98-1c24646112f5

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (q : ℝ) :
    (∑ left : Bool, ∑ right : Bool,
      independentBinaryPairMass q left right) = 1 := by
  simp [Fintype.univ_bool, independentBinaryPairMass, binaryCoinMass]
  ring
end TwoDegenerateGraphs
