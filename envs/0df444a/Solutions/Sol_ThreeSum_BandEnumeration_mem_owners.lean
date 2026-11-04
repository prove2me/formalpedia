-- Prove2me | solution 1 for ThreeSum.BandEnumeration.mem_owners
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:09.051172+00:00
-- url     : https://prove2.me/submissions/0ba1b327-38db-4206-912e-c63792f937d8

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family
namespace ThreeSum.BandEnumeration
theorem _root_.solution (A B C : Family) (o : Owner A B C) : o ∈ owners A B C := by
  rcases o with ⟨j, k⟩ | ⟨i, j | k⟩ <;> simp [owners]
end ThreeSum.BandEnumeration
