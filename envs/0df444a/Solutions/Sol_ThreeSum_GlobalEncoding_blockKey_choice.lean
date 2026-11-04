-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.blockKey_choice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:17:29.279596+00:00
-- url     : https://prove2.me/submissions/24ea88df-8f84-4682-a778-69cc1c634019

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Theorems.Thm_ThreeSum_GlobalEncoding_rawHash_difference

set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
namespace ThreeSum.GlobalEncoding
theorem _root_.solution {h : ℕ} (c : RetainedChoice h) :
    blockKey (blockOfChoice c) = rawRight c - rawLeft c :=
  (rawHash_difference (mapAt h (occurrence c)) (edge c)).symm
end ThreeSum.GlobalEncoding
