-- Prove2me | solution 1 for TwoDegenerateGraphs.independentBinaryPairMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/c9862099-df5a-485a-948b-7edf61e6513f

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binaryCoinMass_nonneg

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution {q : ℝ}
    (hqzero : 0 ≤ q) (hqone : q ≤ 1) (left right : Bool) :
    0 ≤ independentBinaryPairMass q left right := by
  exact mul_nonneg
    (binaryCoinMass_nonneg hqzero hqone left)
    (binaryCoinMass_nonneg hqzero hqone right)
end TwoDegenerateGraphs
