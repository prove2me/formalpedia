-- Prove2me | solution 1 for ThreeSum.TernaryCoverRegularity.source_degree_sq_le_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:44:17.719414+00:00
-- url     : https://prove2.me/submissions/4fc07bd5-54ac-4235-8139-80553d5fd4e1

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_source_degree_le_vertices
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_source_edge_count

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}
namespace ThreeSum.TernaryCoverRegularity
theorem _root_.solution {α π : DigitType} {a : TritWord L} (ha : HasType a α) :
    (Fintype.card (sourceFiber α π a))^2 ≤ Fintype.card (LocalEdge L α π) := by
  rw [source_edge_count ha, pow_two]
  exact Nat.mul_le_mul_right _ (source_degree_le_vertices α π a)
end ThreeSum.TernaryCoverRegularity
