-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPolynomial.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:54:10.827408+00:00
-- url     : https://prove2.me/submissions/83d76457-9337-439d-8083-aea823dd265c

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_tensorIndex_lt
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_body_ends
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_atomExpr_memory
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_atomExpr_safe
import Theorems.Thm_Light_Meets_of_body
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
import Theorems.Thm_ThreeSum_LightMomentDeterminant_body_ends
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
theorem _root_.solution (m base Λ colsBase : ℕ) (cols : PairedIndex m → ℕ)
    (μ : ℕ → ℤ) {lim : Limits} {P : Program} {p depth : ℕ}
    (hp : P[p]?=some (body m)) (hΛ : 1≤Λ) (hbound : ∀ r, cols r<Λ)
    (hcols : ∀ r, μ (colsBase+(Fintype.equivFin (PairedIndex m) r).val)=(cols r : ℤ))
    (hTspace : base+Λ^4≤lim.space) (hCspace : colsBase+Fintype.card (PairedIndex m)≤lim.space)
    (hw : (lim.space : ℤ)≤lim.word)
    (U : ℤ) (hU : 0≤U) (hTabs : ∀ k<Λ^4, |μ (base+k)|≤U)
    (hWord : (polynomial m).coefficient*(U+1)^(polynomial m).degree≤lim.word) :
    Meets lim P p depth [base,Λ,colsBase] μ (time m)
      (fun r ν => r=value (fun q =>
        μ (base+tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2))) ∧ ν=μ) := by
  apply Meets.of_body hp
  apply body_ends m _ _ U hU
  · intro j
    unfold atoms
    split_ifs with hj
    · exact atomExpr_safe m base Λ colsBase cols μ hΛ hbound hcols hTspace hCspace hw _
    · change (0 : ℤ)≤lim.word
      omega
  · intro j
    unfold atoms
    split_ifs with hj
    · rw [atomExpr_memory m base Λ colsBase cols μ hcols]
      exact hTabs _ (tensorIndex_lt (hbound _) (hbound _) (hbound _) (hbound _))
    · simpa [Expr.val] using hU
  · exact hWord
  · exact atomExpr_memory m base Λ colsBase cols μ hcols
end ThreeSum.LightTernaryPairedPolynomial
