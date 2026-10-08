-- Prove2me | solution 1 for TrulySubcubicAPSP.apsp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-06T08:24:07.022217+00:00
-- url     : https://prove2.me/submissions/55d755d7-b5b5-42b7-bb8e-e5b37cf752af

import Theorems.Thm_ThreeSumApsp_wordRam_theorem_22_second
import Theorems.Thm_ThreeSumApsp_WordRam_SolvedInTime_endStatement
import Theorems.Thm_TrulySubcubicAPSP_sourceSpecificationTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem solution : TrulySubcubicAPSP.APSP.SolvedInTime 2.99942 := by
  apply TrulySubcubicAPSP.sourceSpecificationTransport.2.2 2.99942
  exact ThreeSumApsp.wordRam_theorem_22_second.2.2.2.2.endStatement
    (by norm_num) (by norm_num)
