-- Prove2me | solution 1 for ThreeSum.LightBandEnumeration.count_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:38:45.786874+00:00
-- url     : https://prove2.me/submissions/246d4f2d-0fe1-4a8a-a7b1-4e56da11bdad

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
    count a b c ≤ count a' b' c' := by
  unfold count
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul hb hc) (Nat.mul_le_mul ha hb))
    (Nat.mul_le_mul ha hc)
end ThreeSum.LightBandEnumeration
