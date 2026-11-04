-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.representations_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:27.085718+00:00
-- url     : https://prove2.me/submissions/bfbeece9-4522-45cc-b734-539c78c68c69

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Theorems.Thm_ThreeSum_GlobalEncoding_localFiber_nonempty
import Theorems.Thm_ThreeSum_Radix_representations_nonempty


set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
namespace ThreeSum.GlobalEncoding
theorem _root_.solution {h : ℕ} (hh : 0 < h) (J : ℕ) (a b : ℤ) :
    (representations h J a b).Nonempty :=
  Radix.representations_nonempty (localPrime h) rawLeft rawRight
    (localFiber_nonempty hh) J a b
end ThreeSum.GlobalEncoding
