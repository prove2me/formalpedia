-- Prove2me | solution 1 for ThreeSum.QueryCoordinates.positions_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:33:26.78907+00:00
-- url     : https://prove2.me/submissions/61f52b7d-1b54-4e89-83d1-81f34d97d1c5

import Definitions.Def_Submission_ThreeSum_LightWeightedEnumeration
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_Submission_ThreeSum_QueryCoordinates

set_option autoImplicit false
open ThreeSum ThreeSum.QueryCoordinates
open Finset ThreeSum.SubsetAddress
open scoped BigOperators
namespace ThreeSum.QueryCoordinates
theorem _root_.solution {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    (positions Q j).length ≤ j := by
  exact (List.length_filter_le _ _).trans_eq List.length_range
end ThreeSum.QueryCoordinates
