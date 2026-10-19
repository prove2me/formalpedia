-- Prove2me | solution 1 for TwoDegenerateGraphs.withoutReplacementBinaryPairMass_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/ded7cfdb-a462-4789-a052-4ff8d1492090

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (parentCount oneCount : ℕ) (hparents : 2 ≤ parentCount) :
    (∑ left : Bool, ∑ right : Bool,
      withoutReplacementBinaryPairMass parentCount oneCount left right) = 1 := by
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  simp [Fintype.univ_bool,
    withoutReplacementBinaryPairMass, empiricalBinaryOutcomeCount]
  field_simp [hparent_real.ne', hparent_minus.ne']
  ring
end TwoDegenerateGraphs
