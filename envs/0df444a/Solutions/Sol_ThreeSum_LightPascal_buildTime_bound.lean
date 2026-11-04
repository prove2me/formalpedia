-- Prove2me | solution 1 for ThreeSum.LightPascal.buildTime_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:29:53.506136+00:00
-- url     : https://prove2.me/submissions/8417cb97-24f6-4b9d-9a1a-72fd513c7193

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Submission_ThreeSum_LightPascal
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
open ThreeSum ThreeSum.LightPascal
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPascal
theorem _root_.solution (L : ℕ) : buildTime L ≤ 1000*(L+1)^2 := by
  unfold buildTime rowTime LightArray.linearTime
  simp only [fillTime]
  nlinarith
end ThreeSum.LightPascal
