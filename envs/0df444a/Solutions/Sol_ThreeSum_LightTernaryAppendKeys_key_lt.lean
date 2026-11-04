-- Prove2me | solution 1 for ThreeSum.LightTernaryAppendKeys.key_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:34:41.144239+00:00
-- url     : https://prove2.me/submissions/910255c6-b7cd-4cde-a72f-95f1675e4816

import Definitions.Def_Submission_ThreeSum_LightSignedRowHash
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryAppendKeys
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightTernaryAppendKeys
theorem _root_.solution (p power len : ℕ) (old : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (c : ℕ → ℕ) (i : ℕ)
    (hp : 0<p) (ho : old i<power) : key p power len old z c i<power*p := by
  have hm := Nat.mod_lt (LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z i k)) len) hp
  unfold key
  nlinarith
end ThreeSum.LightTernaryAppendKeys
