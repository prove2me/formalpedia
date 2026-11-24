-- Prove2me | solution 1 for ULHC.sidesIn_symmDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:43:59.970327+00:00
-- url     : https://prove2.me/submissions/26ca21e9-9d64-4ab5-b115-a8e7c2c35a82

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
import Theorems.Thm_ULHC_ind_symmDiff

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (A B : Finset Edge) (c : Pt) :
    sidesIn (symmDiff A B) c % 2 = (sidesIn A c + sidesIn B c) % 2 := by
  unfold sidesIn
  have h1 := ind_symmDiff A B (bot c)
  have h2 := ind_symmDiff A B (top c)
  have h3 := ind_symmDiff A B (lft c)
  have h4 := ind_symmDiff A B (rgt c)
  omega
end ULHC
