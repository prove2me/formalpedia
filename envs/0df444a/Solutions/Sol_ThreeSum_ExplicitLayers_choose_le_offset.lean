-- Prove2me | solution 1 for ThreeSum.ExplicitLayers.choose_le_offset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:06:27.073041+00:00
-- url     : https://prove2.me/submissions/64b52a7c-a115-43c4-8d50-d09e15853473

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_ExplicitLayers

set_option autoImplicit false
open ThreeSum ThreeSum.ExplicitLayers
open Finset ThreeSum.SubsetAddress
open scoped BigOperators
namespace ThreeSum.ExplicitLayers
theorem _root_.solution {c j t : ℕ} (hj : j < t) : c.choose j ≤ layerOffset c t := by
  exact Finset.single_le_sum (fun i hi => Nat.zero_le (c.choose i)) (Finset.mem_range.mpr hj)
end ThreeSum.ExplicitLayers
