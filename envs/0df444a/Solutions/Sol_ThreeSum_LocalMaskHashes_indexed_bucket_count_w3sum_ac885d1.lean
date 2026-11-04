-- Prove2me | solution 1 for ThreeSum.LocalMaskHashes.indexed_bucket_count_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:33.390286+00:00
-- url     : https://prove2.me/submissions/aab12c30-7a1b-4964-acc8-752e3c9f1071

import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LocalMaskGraph_setAt_card
import Theorems.Thm_ThreeSum_LocalMaskGraph_setAt_complete
import Theorems.Thm_ThreeSum_LocalMaskGraph_setAt_injective
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
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
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskHashes
open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds
variable {h L k : ℕ}
namespace ThreeSum.LocalMaskHashes
theorem _root_.solution (w : Weight L (LocalField h))
    (shape : Finset (Fin L) → (Fin L → Bool)) (hinj : Function.Injective shape)
    (code : ℕ → ℕ)
    (hcodeLt : ∀ i < LocalMaskGraph.vertexCount L k, code i < localPrime h)
    (hcode : ∀ i < LocalMaskGraph.vertexCount L k,
      (code i : LocalField h) = HashFamily.hashValue w (shape (setAt L k i)))
    {r : ℕ} (hr : r < localPrime h) :
    LightHistogram.count code r (LocalMaskGraph.vertexCount L k) =
      HashFamily.bucketSize ((LayerCounts.vertices L k).image shape) w (r : LocalField h) := by
  unfold LightHistogram.count HashFamily.bucketSize
  apply card_bij (fun i _ => shape (setAt L k i))
  · intro i hi
    obtain ⟨hi,hci⟩ := mem_filter.mp hi
    have hi' := mem_range.mp hi
    refine mem_filter.mpr ⟨mem_image.mpr ⟨setAt L k i,
      LayerCounts.mem_vertices.mpr (setAt_card hi'),rfl⟩,?_⟩
    rw [← hcode i hi',hci]
  · intro i hi j hj he
    exact setAt_injective (mem_range.mp (mem_filter.mp hi).1)
      (mem_range.mp (mem_filter.mp hj).1) (hinj he)
  · intro s hs
    obtain ⟨hs,hhash⟩ := mem_filter.mp hs
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hs
    obtain ⟨i,hi,he⟩ := setAt_complete S (LayerCounts.mem_vertices.mp hS)
    have hcast : (code i : LocalField h) = (r : LocalField h) := by
      rw [hcode i hi,he]
      exact hhash
    have hci : code i = r := by
      have hv := congrArg ZMod.val hcast
      simpa only [ZMod.val_natCast_of_lt (hcodeLt i hi),ZMod.val_natCast_of_lt hr] using hv
    exact ⟨i,mem_filter.mpr ⟨mem_range.mpr hi,hci⟩,congrArg shape he⟩
end ThreeSum.LocalMaskHashes
