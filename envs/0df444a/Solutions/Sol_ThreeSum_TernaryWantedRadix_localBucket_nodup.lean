-- Prove2me | solution 1 for ThreeSum.TernaryWantedRadix.localBucket_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:38.092942+00:00
-- url     : https://prove2.me/submissions/6cefac8f-94cd-4fbe-906c-5d74a51e8dd2

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset
namespace ThreeSum.TernaryWantedRadix
theorem _root_.solution (p : ℤ) (raws : List ℤ) (x : ℤ) : (localBucket p raws x).Nodup :=
  (List.nodup_range).filter _
end ThreeSum.TernaryWantedRadix
