-- Prove2me | solution 1 for ThreeSum.TernaryAddresses.digitCode_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:24:54.799474+00:00
-- url     : https://prove2.me/submissions/fa7f5344-b4d3-4ddf-97a9-7b62cdbc896f

import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryAddresses
open ThreeSum.TernaryEnumeration
namespace ThreeSum.TernaryAddresses
theorem _root_.solution {d e : ℕ} (hd : d < 3) (he : e < 3) (hde : d < e) :
    digitCode d < digitCode e := by
  interval_cases d <;> interval_cases e <;> norm_num [digitCode] at *
end ThreeSum.TernaryAddresses
