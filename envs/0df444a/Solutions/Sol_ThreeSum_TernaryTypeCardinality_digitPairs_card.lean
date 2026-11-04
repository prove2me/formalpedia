-- Prove2me | solution 1 for ThreeSum.TernaryTypeCardinality.digitPairs_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:58.740643+00:00
-- url     : https://prove2.me/submissions/3edc5e7d-b9e4-4954-90ef-a7b7020d2863

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryTypeCardinality
theorem _root_.solution (L a b : ℕ) :
    (digitPairs L a b).card=L.choose b*(L-b).choose a := by
  classical
  unfold digitPairs
  rw [Finset.card_sigma]
  have hlocal (t : Finset (Fin L)) (ht : t∈(univ : Finset (Fin L)).powersetCard b) :
      ((univ\t).powersetCard a).card=(L-b).choose a := by
    obtain ⟨hs,hc⟩ := mem_powersetCard.mp ht
    rw [card_powersetCard,card_sdiff_of_subset hs]
    simp [hc]
  rw [Finset.sum_congr rfl hlocal]
  simp [card_powersetCard,Nat.mul_comm]
end ThreeSum.TernaryTypeCardinality
