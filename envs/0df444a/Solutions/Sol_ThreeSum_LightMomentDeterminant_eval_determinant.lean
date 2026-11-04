-- Prove2me | solution 1 for ThreeSum.LightMomentDeterminant.eval_determinant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:00:53.186219+00:00
-- url     : https://prove2.me/submissions/8d1ce129-3923-4145-a5a1-f33778910ec7

import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
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
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


attribute [local simp] ThreeSum.LightMomentDeterminant.eval_sumCircuits
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_prodCircuits

set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentDeterminant
open Light Matrix ThreeSum.LightFixedArithmetic
open scoped BigOperators
namespace ThreeSum.LightMomentDeterminant
theorem _root_.solution (d : ℕ) (entry : Fin d → Fin d → Circuit) (x : ℕ → ℤ) :
    (determinant d entry).eval x=Matrix.det (Matrix.of (fun i j => (entry i j).eval x)) := by
  classical
  simp only [determinant,eval_sumCircuits,List.map_map,Circuit.eval,eval_prodCircuits,
    Function.comp_apply,Finset.prod_map_toList,Finset.sum_map_toList,Matrix.det_apply',Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp [Function.comp_apply,Circuit.eval,eval_prodCircuits,List.map_map]
end ThreeSum.LightMomentDeterminant
