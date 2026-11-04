-- Prove2me | solution 1 for ThreeSum.TernaryTypeCardinality.vertices_card_eq_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:10:44.369412+00:00
-- url     : https://prove2.me/submissions/49d3a169-e471-47bb-bb56-61d1d6807af0

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_vertices_card_eq_pairs
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_digitPairs_card

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryTypeCardinality
theorem _root_.solution {L : ℕ} (π : DigitType) (htotal : π 0+π 1+π 2=L) :
    (vertices L π).card=L.choose (π 2)*(L-π 2).choose (π 1) := by
  rw [vertices_card_eq_pairs π htotal,digitPairs_card]
end ThreeSum.TernaryTypeCardinality
