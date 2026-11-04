-- Prove2me | solution 1 for ThreeSum.BlockEncoding.leftSubset_disjoint_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:19:53.160519+00:00
-- url     : https://prove2.me/submissions/622bffc3-712a-4175-992e-c20d37b437c2

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Theorems.Thm_ThreeSum_BlockRows_mem_flat
import Theorems.Thm_ThreeSum_LocalGraph_edge_data
attribute [local simp] ThreeSum.BlockRows.mem_flat



set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows
namespace ThreeSum.BlockEncoding
theorem _root_.solution {h J : ℕ} (t : ChoiceTuple h J) :
    Disjoint (leftSubset t) (rightSubset t) := by
  apply Finset.disjoint_left.mpr
  intro ⟨i, x⟩ hL hR
  exact Finset.disjoint_left.mp (edge_data (edge (t i))).2.2
    (mem_flat.mp hL) (mem_flat.mp hR)
end ThreeSum.BlockEncoding
