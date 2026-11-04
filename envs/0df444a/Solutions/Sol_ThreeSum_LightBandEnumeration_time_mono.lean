-- Prove2me | solution 1 for ThreeSum.LightBandEnumeration.time_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:58:35.986201+00:00
-- url     : https://prove2.me/submissions/54f2e6eb-3678-4e82-aa23-b69eb6fb98f3

import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Theorems.Thm_ThreeSum_LightBandEnumeration_width_mono

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandEnumeration
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandEnumeration
theorem _root_.solution {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    time a b c ≤ time a' b' c' := by
  have hw := width_mono ha hb hc
  have hlog := Nat.clog_mono_right 2 (show a+b+c+1 ≤ a'+b'+c'+1 by omega)
  unfold time clog2Time powTableTime LightBandTable.time LightBandTable.rowTime
    LightBandLookup.time LightBandLookup.searchTime
  gcongr
end ThreeSum.LightBandEnumeration
