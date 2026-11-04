-- Prove2me | solution 1 for ThreeSum.BandRawA.product_original_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:05.530226+00:00
-- url     : https://prove2.me/submissions/cad86d40-3477-4fa6-97bf-65c6b71466b0

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
import Definitions.Def_WeightedCache3SUM_Alias_916a22962ee73517

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition Finset
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ allProducts A.length B.length C.length g rs) :
    valueAt A.length g rs (fun i => A.getD i 0) t.1 ∈ originalA ∧
      B.getD t.2.1 0 ∈ originalB ∧ C.getD t.2.2 0 ∈ originalC := by
  obtain ⟨ha,hb,hc⟩ := product_values_mem ht
  exact ⟨(hA _).mp ha,(hB _).mp hb,(hC _).mp hc⟩
end ThreeSum.BandRawA
