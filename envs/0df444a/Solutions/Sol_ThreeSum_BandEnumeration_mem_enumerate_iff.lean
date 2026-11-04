-- Prove2me | solution 1 for ThreeSum.BandEnumeration.mem_enumerate_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:16.670874+00:00
-- url     : https://prove2.me/submissions/9c16a4da-1e16-47ff-91fa-8671db875d0e

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Theorems.Thm_ThreeSum_BandEnumeration_checkedCandidate_sound
import Theorems.Thm_ThreeSum_BandEnumeration_checkedCandidate_complete
import Theorems.Thm_ThreeSum_BandEnumeration_mem_owners

set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family
namespace ThreeSum.BandEnumeration
theorem _root_.solution (A B C : Family) (t : Triple A B C) :
    t ∈ enumerate A B C ↔ relevant A B C t := by
  constructor
  · intro h
    obtain ⟨o, _, heq⟩ := List.mem_filterMap.mp h
    exact (checkedCandidate_sound A B C o heq).1
  · intro h
    exact List.mem_filterMap.mpr ⟨owner A B C t, mem_owners A B C _,
      checkedCandidate_complete A B C t h⟩
end ThreeSum.BandEnumeration
