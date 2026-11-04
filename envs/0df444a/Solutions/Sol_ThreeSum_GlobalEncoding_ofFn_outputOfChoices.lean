-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.ofFn_outputOfChoices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:33.863681+00:00
-- url     : https://prove2.me/submissions/08f9e231-9588-493d-8745-e1ba008092ff

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding

set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
namespace ThreeSum.GlobalEncoding
theorem _root_.solution {h J : ℕ} (xs : List (RetainedChoice h))
    (hlen : xs.length = J) :
    List.ofFn (outputOfChoices xs hlen) = xs.map blockOfChoice := by
  subst J
  exact List.ofFn_getElem_eq_map xs blockOfChoice
end ThreeSum.GlobalEncoding
