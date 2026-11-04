-- Prove2me | solution 1 for ThreeSum.LightSwitchScalar.pow_cost_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:03.778285+00:00
-- url     : https://prove2.me/submissions/47599d39-533c-4330-a6fc-43f7d6cf1772

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar

set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchScalar
open Light
set_option maxHeartbeats 1600000
namespace ThreeSum.LightSwitchScalar
theorem _root_.solution (B a b : ℕ) (hB : 1 ≤ B) : B^b ≤ B^(a+b+1) :=
  Nat.pow_le_pow_right hB (by omega)
end ThreeSum.LightSwitchScalar
