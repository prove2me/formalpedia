-- Prove2me | solution 1 for ThreeSum.LightScales.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:02:25.785941+00:00
-- url     : https://prove2.me/submissions/d2bc4a91-7041-435b-99df-842814b1a342

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
import Theorems.Thm_Light_cbrtLeast_le_self
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightScales
theorem _root_.solution (n : ℕ) : time n ≤ 500*(inputBits n+1) := by
  have hu := cbrtLeast_le_self (inputBits n+1)
  have hh := Nat.div_le_self (cbrtLeast (inputBits n+1)+1) 2
  have hq := Nat.div_le_self (inputBits n) (100*muZero n)
  unfold time log2Time cbrtCeilTime halfTime LightSmallDivide.time
  simp only [inputBits,Nat.log2_eq_log_two] at *
  omega
end ThreeSum.LightScales
