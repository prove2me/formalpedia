-- Prove2me | solution 1 for ThreeSum.TernaryTypeCardinality.vertices_card_eq_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:06:58.257336+00:00
-- url     : https://prove2.me/submissions/2290e152-eddc-4f69-9d27-dd1453a7b712

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_encode_injective
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_mem_digitPairs
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_encode_mem
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_encode_decode
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_decode_hasType

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryTypeCardinality
theorem _root_.solution {L : ℕ} (π : DigitType) (htotal : π 0+π 1+π 2=L) :
    (vertices L π).card=(digitPairs L (π 1) (π 2)).card := by
  classical
  apply Finset.card_bij (fun w _ => encode w)
  · intro w hw
    exact encode_mem π (mem_filter.mp hw).2
  · intro w hw v hv he
    exact encode_injective L he
  · intro p hp
    have hh := (mem_digitPairs p).mp hp
    exact ⟨decode p,mem_filter.mpr ⟨mem_univ _,decode_hasType π htotal p hp⟩,
      encode_decode p hh.2.2⟩
end ThreeSum.TernaryTypeCardinality
