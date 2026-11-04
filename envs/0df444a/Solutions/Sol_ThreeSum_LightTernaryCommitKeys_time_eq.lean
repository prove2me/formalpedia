-- Prove2me | solution 1 for ThreeSum.LightTernaryCommitKeys.time_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:24.859425+00:00
-- url     : https://prove2.me/submissions/cf221eb3-59d3-445e-a576-0c8534796683

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitKeys
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
open ThreeSum ThreeSum.LightTernaryCommitKeys
open Light
set_option maxHeartbeats 2000000
namespace ThreeSum.LightTernaryCommitKeys
theorem _root_.solution (nB nC nO : ℕ) : time nB nC nO=16*(nB+nC+nO)+118 := by
  simp [time,copyTime]
  omega
end ThreeSum.LightTernaryCommitKeys
