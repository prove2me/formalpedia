-- Prove2me | solution 1 for ValueAwareRR.residualMax_eq_familyA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:10:04.09529+00:00
-- url     : https://prove2.me/submissions/e8ce1b55-0397-42d7-a739-0eca7bb35589

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (hm : 2 ≤ m) :
    residualMax m = familyA m := by
  change max |-familyA m|
    (max |-familyB m| (max |familyB m| |familyA m|)) = familyA m
  norm_num [familyA, familyB]
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> nlinarith
end ValueAwareRR
