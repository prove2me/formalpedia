-- Prove2me | solution 1 for ThreeSum.LocalCoverMatrix.entry_eq_one_iff_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:30:45.059024+00:00
-- url     : https://prove2.me/submissions/ab155159-ebe4-4a47-b53d-33e403ff20ac

import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
import Theorems.Thm_ThreeSum_LocalCoverMatrix_radix_div
import Theorems.Thm_ThreeSum_LocalCoverMatrix_radix_mod
import Theorems.Thm_ThreeSum_LocalCoverMatrix_radix_injective
import Theorems.Thm_ThreeSum_LocalCoverMatrix_covers_iff_edge
import Theorems.Thm_ThreeSum_LocalCoverMatrix_valid_iff
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
import Theorems.Thm_ThreeSum_LocalGraph_edge_data
import Theorems.Thm_ThreeSum_LocalMaskGraph_setAt_card
import Theorems.Thm_ThreeSum_LocalMaskGraph_setAt_complete
import Theorems.Thm_ThreeSum_LocalMaskHashes_leftCode_cast
import Theorems.Thm_ThreeSum_LocalMaskHashes_leftCode_val
import Theorems.Thm_ThreeSum_LocalMaskHashes_left_count
import Theorems.Thm_ThreeSum_LocalMaskHashes_rightCode_cast
import Theorems.Thm_ThreeSum_LocalMaskHashes_rightCode_lt
import Theorems.Thm_ThreeSum_LocalMaskHashes_rightCode_val
import Theorems.Thm_ThreeSum_LocalMaskHashes_right_count
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
open ThreeSum ThreeSum.LocalCoverMatrix
open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes
variable {h L k : ℕ}
namespace ThreeSum.LocalCoverMatrix
theorem _root_.solution (w : Weight L (LocalField h)) {B a b : ℕ}
    (ha : a < localPrime h) (hb : b < localPrime h) :
    entry w k B (a*localPrime h+b)=1 ↔
      Covers L k B w ((a : LocalField h),(b : LocalField h)) := by
  have hbit : entry w k B (a*localPrime h+b)=1 ↔
      LightSupportMark.Hit (key w k) (valid w k B) (a*localPrime h+b)
        (LocalMaskGraph.vertexCount L k*LocalMaskGraph.vertexCount L k) := by
    unfold entry LightSupportMark.bit
    split <;> simp_all
  rw [hbit,covers_iff_edge]
  constructor
  · rintro ⟨i,hi,hvalid,hkey⟩
    have hi' := mem_range.mp hi
    have hn : 0 < LocalMaskGraph.vertexCount L k := by nlinarith
    have hq : i/LocalMaskGraph.vertexCount L k < LocalMaskGraph.vertexCount L k :=
      (Nat.div_lt_iff_lt_mul hn).mpr hi'
    have hr := Nat.mod_lt i hn
    obtain ⟨hdisj,hleft,hright⟩ := (valid_iff w hi').mp hvalid
    obtain ⟨hca,hcb⟩ := radix_injective (rightCode_lt w k _) hb hkey
    let e : LocalGraph.Edge L k :=
      ⟨(setAt L k (i/LocalMaskGraph.vertexCount L k),
        setAt L k (i%LocalMaskGraph.vertexCount L k)),
        LayerCounts.mem_edgeSet.mpr ⟨setAt_card hq,setAt_card hr,hdisj⟩⟩
    refine ⟨e,?_,?_,?_,?_⟩
    · exact (leftCode_cast w hq).symm.trans (congrArg (fun n : ℕ => (n : LocalField h)) hca)
    · exact (rightCode_cast w hr).symm.trans (congrArg (fun n : ℕ => (n : LocalField h)) hcb)
    · change LightHistogram.count _ _ _ ≤ B at hleft
      rw [hca,left_count w ha] at hleft
      exact hleft
    · change LightHistogram.count _ _ _ ≤ B at hright
      rw [hcb,right_count w hb] at hright
      exact hright
  · rintro ⟨e,hleftHash,hrightHash,hleft,hright⟩
    obtain ⟨i,hi,hei⟩ := setAt_complete e.val.1 (LocalGraph.edge_data e).1
    obtain ⟨j,hj,hej⟩ := setAt_complete e.val.2 (LocalGraph.edge_data e).2.1
    have hn : 0 < LocalMaskGraph.vertexCount L k := by omega
    have hidx : i*LocalMaskGraph.vertexCount L k+j <
        LocalMaskGraph.vertexCount L k*LocalMaskGraph.vertexCount L k := by nlinarith
    have hq := radix_div hj (a := i)
    have hr := radix_mod hj (a := i)
    have hca : leftCode w k i=a := by
      rw [leftCode_val w hi,hei]
      change (HashFamily.hashValue w (LocalGraph.left e)).val=a
      rw [hleftHash,ZMod.val_natCast_of_lt ha]
    have hcb : rightCode w k j=b := by
      rw [rightCode_val w hj,hej]
      change (HashFamily.hashValue w (LocalGraph.right e)).val=b
      rw [hrightHash,ZMod.val_natCast_of_lt hb]
    refine ⟨i*LocalMaskGraph.vertexCount L k+j,mem_range.mpr hidx,?_,?_⟩
    · rw [valid_iff w hidx,hq,hr,hei,hej,hca,hcb]
      refine ⟨(LocalGraph.edge_data e).2.2,?_,?_⟩
      · simpa only [leftCount,left_count w ha] using hleft
      · simpa only [rightCount,right_count w hb] using hright
    · unfold key LightPairFlags.pairKey
      rw [hq,hr,hca,hcb]
end ThreeSum.LocalCoverMatrix
