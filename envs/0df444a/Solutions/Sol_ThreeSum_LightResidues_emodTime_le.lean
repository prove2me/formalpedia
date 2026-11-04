-- Prove2me | solution 1 for ThreeSum.LightResidues.emodTime_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:28:32.819095+00:00
-- url     : https://prove2.me/submissions/0342e487-23f1-466c-b422-1973b40c292e

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightResidues
import Theorems.Thm_Light_emodRounds_le
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
open ThreeSum ThreeSum.LightResidues
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightResidues
theorem _root_.solution {x : ℤ} {p U : ℕ} (hx : |x| ≤ (U : ℤ)) :
    emodTime x.natAbs p ≤ residueBudget U := by
  have hU : x.natAbs ≤ U := by simpa only [← Int.natCast_natAbs, Nat.cast_le] using hx
  have h := emodRounds_le (M := p) hU
  unfold emodTime residueBudget
  omega
end ThreeSum.LightResidues
