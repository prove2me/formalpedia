-- Prove2me | solution 1 for ThreeSum.LightSourceTrim.rowFlag_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:53:55.203244+00:00
-- url     : https://prove2.me/submissions/166f7442-d0a3-4462-a561-0432106927b7

import Definitions.Def_Submission_ThreeSum_LightSourceRowFlag
import Definitions.Def_Submission_ThreeSum_SourceFlagProduct
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Theorems.Thm_ThreeSum_LightSourceFlagTest_flag_le
import Theorems.Thm_ThreeSum_LightSourceRowFlag_flag_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceTrim
open Light SourceFlagProduct
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
namespace ThreeSum.LightSourceTrim
theorem _root_.solution (L h p cap : ℕ) (sel candidate bits : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (j : ℕ) :
    rowFlag L h p cap sel candidate bits w0 w1 counts j ≤ 1 :=
  LightSourceRowFlag.flag_le ..
end ThreeSum.LightSourceTrim
