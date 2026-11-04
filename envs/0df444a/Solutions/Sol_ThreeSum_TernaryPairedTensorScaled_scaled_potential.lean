-- Prove2me | solution 1 for ThreeSum.TernaryPairedTensorScaled.scaled_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:49.092959+00:00
-- url     : https://prove2.me/submissions/a9b18090-aea6-424a-9085-ca62dcecdaa3

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatch
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensorScaled
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
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_value_scaled
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_digit
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_divide
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_main
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_polynomial
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_powers
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_row
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
import Theorems.Thm_ThreeSum_TernaryPairedColumnEnumeration_sum_digits_eq_sum_columns
import Theorems.Thm_ThreeSum_TernaryPairedTensor_full_potential_tensor_expansion
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
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_prodCircuits
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_sumCircuits
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_digit
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_divide
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_main
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_polynomial
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_powers
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_row
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
open ThreeSum ThreeSum.TernaryPairedTensorScaled
open LightTernaryPairedPolynomial LightTernaryPairedPotential
open TernaryPairedTensor TernaryPairedColumnEnumeration
open scoped BigOperators
namespace ThreeSum.TernaryPairedTensorScaled
theorem _root_.solution {P : Type*} [Fintype P]
    (K base Λ : ℕ) (μ : ℕ→ℤ) (L R : P→Fin Λ→ℤ) (s : ℤ)
    (hTensor : ∀ a b c d : Fin Λ,
      μ (base+tensorIndex Λ a.val b.val c.val d.val)=s*tensor L R a b c d) :
    prefixSum K base Λ μ (Λ^width K)=s^K*
      ((∑ e : Fin K→P, TernaryPairedPotential.rowWeight
        (Sum.elim (fun i => L (e i)) (fun i => R (e i)))) : ℤ) := by
  unfold prefixSum term
  change (∑ i∈Finset.range (Λ^width K),
    (fun cols : PairedIndex K→ℕ => value (fun q =>
      μ (base+tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2))))
      (fun r => WeightEnumeration.digit Λ (width K) i (Fintype.equivFin (PairedIndex K) r).val)) = _
  have he := sum_digits_eq_sum_columns K Λ
    (fun cols : PairedIndex K→ℕ => value (fun q =>
      μ (base+tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2))))
  refine he.trans ?_
  calc
    _ = ∑ cols : PairedIndex K→Fin Λ, s^K*value (fun q => tensor L R (cols q.1)
        (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2)) := by
      apply Finset.sum_congr rfl
      intro cols hcols
      have he : (fun q : Quad K => μ (base+tensorIndex Λ (cols q.1).val
          (cols q.2.1).val (cols q.2.2.1).val (cols q.2.2.2).val))=
          (fun q => s*tensor L R (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2)) := by
        funext q
        exact hTensor _ _ _ _
      rw [he,value_scaled]
    _ = s^K*∑ cols : PairedIndex K→Fin Λ, value (fun q => tensor L R (cols q.1)
        (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2)) := (Finset.mul_sum _ _ _).symm
    _ = _ := by
      congr 1
      simpa [value,channel] using (full_potential_tensor_expansion (m := K) L R).symm
end ThreeSum.TernaryPairedTensorScaled
