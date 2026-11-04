-- Prove2me | solution 1 for ThreeSum.LightRadixKeys.word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:33:46.62371+00:00
-- url     : https://prove2.me/submissions/4a1c7ca2-84dd-4344-85a8-2d9928b06819

import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Definitions.Def_Submission_ThreeSum_LightRadixKeys

set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixKeys
open Light RadixKeyLists
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThreeSum.LightRadixKeys
theorem _root_.solution {p U j k : ℕ} (hj : j ≤ k) : word p U j ≤ word p U k := by
  have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ p+1) hj
  have hv := Nat.mul_le_mul_left U hpow
  have hpv := Nat.mul_le_mul_left p hv
  unfold word LightRadixRows.word
  omega
end ThreeSum.LightRadixKeys
