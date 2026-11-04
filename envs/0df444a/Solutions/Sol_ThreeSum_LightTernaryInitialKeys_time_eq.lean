-- Prove2me | solution 1 for ThreeSum.LightTernaryInitialKeys.time_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:23.659787+00:00
-- url     : https://prove2.me/submissions/8fdbc496-4189-4709-bc89-9e5556dbab38

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialKeys
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryInitialKeys
open Light
set_option maxHeartbeats 2000000
namespace ThreeSum.LightTernaryInitialKeys
theorem _root_.solution (nB nC nO : ℕ) : time nB nC nO=13*(nB+nC+nO)+118 := by
  simp [time,fillTime]
  omega
end ThreeSum.LightTernaryInitialKeys
