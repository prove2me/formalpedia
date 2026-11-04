-- Prove2me | solution 1 for ThreeSum.QueryCoordinates.positions_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:50:50.969098+00:00
-- url     : https://prove2.me/submissions/1ab280a6-9064-4105-bdfe-18d0c5de3163

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
    (positions Q j).Nodup := List.nodup_range.filter _
end ThreeSum.QueryCoordinates
