-- Prove2me | solution 1 for ThreeSum.BandRawA.product_values_mem_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:19.620505+00:00
-- url     : https://prove2.me/submissions/80f83f82-c680-4090-a3d9-b2202cca8b71

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
import Theorems.Thm_ThreeSum_BandRawA_at_mem
import Theorems.Thm_ThreeSum_BandRawA_bandPositions_lt
import Definitions.Def_WeightedCache3SUM_Alias_8fa29246dc9d5286
import Theorems.Thm_ThreeSum_BandRawA_position_lt
import Theorems.Thm_ThreeSum_BandRawA_values_getD
import Theorems.Thm_ThreeSum_BandWeightedScore_position_lt


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition Finset
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution {A B C : List ℤ} {g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts A.length B.length C.length g rs) :
    valueAt A.length g rs (fun i => A.getD i 0) t.1 ∈ A ∧
      B.getD t.2.1 0 ∈ B ∧ C.getD t.2.2 0 ∈ C := by
  obtain ⟨ha,hb,hc⟩ := mem_allProducts.mp ht
  have hap := position_lt (at_mem ha)
  have hbp := bandPositions_lt hb
  have hcp := bandPositions_lt hc
  refine ⟨?_,?_,?_⟩
  · rw [valueAt,values_getD _ ha,List.getD_eq_getElem _ _ hap]
    exact List.getElem_mem hap
  · rw [List.getD_eq_getElem _ _ hbp]
    exact List.getElem_mem hbp
  · rw [List.getD_eq_getElem _ _ hcp]
    exact List.getElem_mem hcp
end ThreeSum.BandRawA
