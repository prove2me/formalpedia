-- Prove2me | solution 1 for ThreeSum.LightSwitchScalar.pow_cost_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:02.499849+00:00
-- url     : https://prove2.me/submissions/4a30eed1-848d-4744-b1db-62ab82e43e39

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar

set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchScalar
open Light
set_option maxHeartbeats 1600000
namespace ThreeSum.LightSwitchScalar
theorem _root_.solution (B a b : ℕ) (hB : 1 ≤ B) : B^a ≤ B^(a+b+1) :=
  Nat.pow_le_pow_right hB (by omega)
end ThreeSum.LightSwitchScalar
