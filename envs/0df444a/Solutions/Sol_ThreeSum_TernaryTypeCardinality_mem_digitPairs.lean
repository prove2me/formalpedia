-- Prove2me | solution 1 for ThreeSum.TernaryTypeCardinality.mem_digitPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:00.523519+00:00
-- url     : https://prove2.me/submissions/57cf33de-2ee7-4621-b934-336e8de02b67

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
theorem _root_.solution {L a b : ℕ} (p : Pair L) :
    p∈digitPairs L a b ↔ p.1.card=b ∧ p.2.card=a ∧ Disjoint p.1 p.2 := by
  classical
  simp only [digitPairs,mem_sigma,mem_powersetCard]
  constructor
  · rintro ⟨⟨ht,hb⟩,⟨ho,ha⟩⟩
    refine ⟨hb,ha,Finset.disjoint_left.mpr ?_⟩
    intro i hiT hiO
    exact (mem_sdiff.mp (ho hiO)).2 hiT
  · rintro ⟨hb,ha,hd⟩
    refine ⟨⟨subset_univ _,hb⟩,⟨?_,ha⟩⟩
    intro i hiO
    exact mem_sdiff.mpr ⟨mem_univ _,fun hiT => Finset.disjoint_left.mp hd hiT hiO⟩
end ThreeSum.TernaryTypeCardinality
