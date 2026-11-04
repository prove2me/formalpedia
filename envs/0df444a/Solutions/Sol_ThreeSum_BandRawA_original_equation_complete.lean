-- Prove2me | solution 1 for ThreeSum.BandRawA.original_equation_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:09.149719+00:00
-- url     : https://prove2.me/submissions/b9cfe35a-647e-457e-9cd4-4bf46f71b8ad

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
import Theorems.Thm_ThreeSum_BandRawA_sorted_equation_complete

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition Finset
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {a b c : ℤ} (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ha : a ∈ originalA) (hb : b ∈ originalB) (hc : c ∈ originalC) (heq : a+b=c) :
    ∃ t ∈ allProducts A.length B.length C.length g (sortedRecords A B C g hg hsA hsB hsC),
      valueAt A.length g (sortedRecords A B C g hg hsA hsB hsC)
        (fun i => A.getD i 0) t.1=a ∧ B.getD t.2.1 0=b ∧ C.getD t.2.2 0=c :=
  sorted_equation_complete hg hsA hsB hsC ((hA a).mpr ha) ((hB b).mpr hb) ((hC c).mpr hc) heq
end ThreeSum.BandRawA
