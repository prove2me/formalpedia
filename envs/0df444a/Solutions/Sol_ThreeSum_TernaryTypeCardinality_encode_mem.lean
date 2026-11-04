-- Prove2me | solution 1 for ThreeSum.TernaryTypeCardinality.encode_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:01:59.544799+00:00
-- url     : https://prove2.me/submissions/0d3f0e22-2c70-447a-9f0c-2d82326feb9c

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_positions_card
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_positions_disjoint
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_mem_digitPairs

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryTypeCardinality
theorem _root_.solution {L : ℕ} (π : DigitType) {w : TritWord L} (hw : HasType w π) :
    encode w∈digitPairs L (π 1) (π 2) := by
  rw [mem_digitPairs]
  refine ⟨?_,?_,positions_disjoint w⟩
  · change (positions w 2).card=π 2
    rw [positions_card]
    exact hw 2
  · change (positions w 1).card=π 1
    rw [positions_card]
    exact hw 1
end ThreeSum.TernaryTypeCardinality
