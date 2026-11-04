-- Prove2me | solution 1 for ThreeSum.LightScales.cbrtLeast_successor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:37:51.809637+00:00
-- url     : https://prove2.me/submissions/885d7242-0bb3-410a-bcc5-ae39a3f5fe71

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
import Theorems.Thm_Light_cbrtLeast_le
import Theorems.Thm_Light_le_cbrtLeast_pow


set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightScales
theorem _root_.solution (m : ℕ) : cbrtLeast (m+1) = Nat.nthRoot 3 m+1 := by
  have hlo : Nat.nthRoot 3 m ^ 3 ≤ m := Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0))
  have hhi : m < (Nat.nthRoot 3 m+1)^3 := Nat.lt_pow_nthRoot_add_one (by decide) m
  have hup : cbrtLeast (m+1) ≤ Nat.nthRoot 3 m+1 := cbrtLeast_le (by omega)
  have hstrict : Nat.nthRoot 3 m < cbrtLeast (m+1) := by
    by_contra h
    have hp := Nat.pow_le_pow_left (show cbrtLeast (m+1) ≤ Nat.nthRoot 3 m by omega) 3
    have hneed := le_cbrtLeast_pow (m+1)
    omega
  omega
end ThreeSum.LightScales
