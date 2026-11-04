-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.globalKey_outputOfChoices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:26:08.33002+00:00
-- url     : https://prove2.me/submissions/a2071303-5394-4817-b4c3-dcbe897c496e

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Theorems.Thm_ThreeSum_GlobalEncoding_positionalHash_difference
import Theorems.Thm_ThreeSum_GlobalEncoding_ofFn_outputOfChoices

set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
namespace ThreeSum.GlobalEncoding
theorem _root_.solution {h J : ℕ} (xs : List (RetainedChoice h))
    (hlen : xs.length = J) :
    globalKey (outputOfChoices xs hlen) =
      Radix.positionalHash (localPrime h) rawRight xs -
        Radix.positionalHash (localPrime h) rawLeft xs := by
  rw [globalKey, ofFn_outputOfChoices, positionalHash_difference]
end ThreeSum.GlobalEncoding
