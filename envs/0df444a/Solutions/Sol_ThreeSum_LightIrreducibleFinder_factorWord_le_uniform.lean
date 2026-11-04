-- Prove2me | solution 1 for ThreeSum.LightIrreducibleFinder.factorWord_le_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:41:07.10839+00:00
-- url     : https://prove2.me/submissions/4b50c7e5-a463-4b0a-8039-6179c8bfaee3

import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
import Definitions.Def_Submission_ThreeSum_LightIrreducibleBudget
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
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_program_length
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
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
attribute [local simp] ThreeSum.LightIrreducibleFinder.program_length
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightIrreducibleFinder
open Light
set_option maxHeartbeats 3000000
namespace ThreeSum.LightIrreducibleFinder
theorem _root_.solution (C : LightExtensionFactorPredicate.Layout) (q e : ℕ)
    (hp : 1 ≤ C.p) (he : e ≤ C.dim) (hq : C.p^C.dim=q) :
    LightExtensionFactorPredicate.word (atDegree C e) q q ≤ uniformFactorWord C.dim C.p q := by
  have hpe : C.p^e ≤ q := by rw [←hq]; exact Nat.pow_le_pow_right hp he
  have hpr : C.p^(C.dim-e) ≤ q := by rw [←hq]; exact Nat.pow_le_pow_right hp (Nat.sub_le _ _)
  have hm := Nat.mul_le_mul_right ((C.p+1)^2) (show e+2 ≤ C.dim+2 by omega)
  unfold LightExtensionFactorPredicate.word LightExtensionFactorCheck.word
    uniformFactorWord LightCoefficientDecode.word atDegree
  dsimp only
  omega
end ThreeSum.LightIrreducibleFinder
