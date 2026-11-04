-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPolynomial.value_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:35:49.922653+00:00
-- url     : https://prove2.me/submissions/42ff9090-0bba-4591-b55c-9fefa805b782

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_polynomial_eval
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_eval_abs_le
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_prodCircuits
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_sumCircuits
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPolynomial
theorem _root_.solution {m : ℕ} (T : Quad m → ℤ) (U : ℤ) (hU : 0≤U)
    (hT : ∀ q, |T q|≤U) : |value T|≤(polynomial m).bound U := by
  let x := fun j => if hj : j<Fintype.card (Quad m) then
    T ((Fintype.equivFin (Quad m)).symm ⟨j,hj⟩) else 0
  have he (q : Quad m) : x (encode q)=T q := by
    dsimp [x,encode]
    rw [if_pos (Fintype.equivFin (Quad m) q).isLt]
    simp
  have hp : (polynomial m).eval x=value T := by
    rw [polynomial_eval]
    apply Finset.sum_congr rfl
    intro σ hσ
    apply Finset.sum_congr rfl
    intro τ hτ
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact he _
  rw [←hp]
  apply (polynomial m).eval_abs_le x hU
  intro j
  dsimp [x]
  split_ifs
  · exact hT _
  · simpa using hU
end ThreeSum.LightTernaryPairedPolynomial
