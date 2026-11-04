-- Prove2me | solution 1 for ThreeSum.SignedLeaf.explicitMissing_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:56:50.239975+00:00
-- url     : https://prove2.me/submissions/21be4a66-c471-4ca5-8cd2-15473c16efd0

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_mem
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_nodup


set_option autoImplicit false
open ThreeSum ThreeSum.SignedLeaf
open Finset ThreeSum.SubsetAddress
open scoped BigOperators
namespace ThreeSum.SignedLeaf
theorem _root_.solution {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) :
    (explicitMissing Q t).Nodup := by
  rw [explicitMissing,List.nodup_flatMap]
  constructor
  · intro j hj
    exact QueryCoordinates.missingSets_nodup Q j
  · refine (List.nodup_range (n := t)).imp ?_
    intro a b hab
    apply List.disjoint_left.mpr
    intro U hU hV
    have h₁ := (QueryCoordinates.missingSets_mem Q U a).mp hU
    have h₂ := (QueryCoordinates.missingSets_mem Q U b).mp hV
    omega
end ThreeSum.SignedLeaf
