-- Prove2me | solution 1 for ThreeSum.LightDownsetEnumeration.time_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:56:58.814354+00:00
-- url     : https://prove2.me/submissions/1bff396e-cef5-488b-ac02-0e4964d4bf58

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDownsetEnumeration
theorem _root_.solution {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 1000*(L+1)^2*(downsetCap L cut+1) := by
  have hb : budget L cut+70 ≤ 800*(L+1)*(downsetCap L cut+1) := by
    unfold budget
    nlinarith
  have hm := Nat.mul_le_mul_left (cut+1) hb
  have hc := Nat.mul_le_mul_right (800*(L+1)*(downsetCap L cut+1))
    (Nat.succ_le_succ hcut)
  have hp : 1 ≤ (L+1)^2*(downsetCap L cut+1) :=
    Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by omega)) (by omega))
  unfold time
  calc
    _ ≤ (L+1)*(800*(L+1)*(downsetCap L cut+1))+40 := Nat.add_le_add_right (hm.trans hc) 40
    _ = 800*((L+1)^2*(downsetCap L cut+1))+40 := by ring
    _ ≤ 1000*((L+1)^2*(downsetCap L cut+1)) := by omega
    _ = _ := by ring
end ThreeSum.LightDownsetEnumeration
