-- Prove2me | solution 1 for ThreeSum.BandRawA.original_equation_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:56:28.921678+00:00
-- url     : https://prove2.me/submissions/306bb3db-7a49-4df3-bef3-93bcd5423abb

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
import Theorems.Thm_ThreeSum_BandRawA_product_original_values

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
    (ht : t ∈ allProducts A.length B.length C.length g rs)
    (heq : valueAt A.length g rs (fun i => A.getD i 0) t.1+B.getD t.2.1 0=C.getD t.2.2 0) :
    ∃ a ∈ originalA, ∃ b ∈ originalB, ∃ c ∈ originalC, a+b=c := by
  obtain ⟨ha,hb,hc⟩ := product_original_values hA hB hC ht
  exact ⟨_,ha,_,hb,_,hc,heq⟩
end ThreeSum.BandRawA
