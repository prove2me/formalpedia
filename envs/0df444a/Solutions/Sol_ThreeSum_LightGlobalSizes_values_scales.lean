-- Prove2me | solution 1 for ThreeSum.LightGlobalSizes.values_scales
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:45:19.203783+00:00
-- url     : https://prove2.me/submissions/25de8b2b-3502-4b67-9709-34cd3c5410af

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_BandScales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightGlobalSizes
import Theorems.Thm_ThreeSum_LightGlobalSizes_localCount_pow
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalSizes
set_option maxHeartbeats 1000000
open Light LocalCoverBounds
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightGlobalSizes
theorem _root_.solution (n : ℕ) :
    values (localCount n) (Scales.localRadix n) (Scales.blockCount (Scales.inputBits n)) (Scales.mu n) =
      [(Scales.typedOutputs n : ℤ),Scales.radix n,BandScales.bandRoot n,
        BandScales.bandDivisor n,BandScales.bandSize n] := by
  simp only [values,root,localCount_pow,divisor,band,numerator,
    Scales.radix,BandScales.bandRoot,BandScales.bandDivisor,BandScales.bandSize,Nat.ceilDiv_eq_add_pred_div]
end ThreeSum.LightGlobalSizes
