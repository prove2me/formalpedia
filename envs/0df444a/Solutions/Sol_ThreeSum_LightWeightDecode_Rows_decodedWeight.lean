-- Prove2me | solution 1 for ThreeSum.LightWeightDecode.Rows.decodedWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:43:56.215385+00:00
-- url     : https://prove2.me/submissions/2640d838-2a28-4ea2-a06e-c4a012f90a2c

import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightWeightDecode
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_WeightEnumeration_decodedWeight_val
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightDecode
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightWeightDecode
namespace Rows
theorem _root_.solution {μ : ℕ → ℤ} {dst L p k : ℕ}
    (hrows : Rows μ dst L p k) (i : Fin L) :
    μ (dst+i.val) = ((WeightEnumeration.decodedWeight (K := ZMod p) L p k (i,false)).val : ℤ) ∧
    μ (dst+L+i.val) = ((WeightEnumeration.decodedWeight (K := ZMod p) L p k (i,true)).val : ℤ) := by
  simpa only [WeightEnumeration.decodedWeight_val,WeightEnumeration.coordinateIndex,
    Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] using hrows i.val i.isLt
end Rows
end ThreeSum.LightWeightDecode
