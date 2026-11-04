-- Prove2me | solution 1 for ThreeSum.LightBandEnumeration.width_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:55:00.826736+00:00
-- url     : https://prove2.me/submissions/55a1107f-e6db-4e4f-9bef-468d85e72e48

import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandEnumeration
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandEnumeration
theorem _root_.solution {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    width a b c ≤ width a' b' c' := Nat.clog_mono_right 2 (by omega)
end ThreeSum.LightBandEnumeration
