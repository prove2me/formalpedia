-- Prove2me | solution 1 for ThreeSum.TernaryCoverRegularity.source_degree_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:11.385006+00:00
-- url     : https://prove2.me/submissions/a7a5d7cb-fb26-447d-972c-25c447a4546e

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_source_degree_sq_le_edges

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}
namespace ThreeSum.TernaryCoverRegularity
theorem _root_.solution {α π : DigitType} {a : TritWord L} (ha : HasType a α)
    (P : ℕ) (hE : Fintype.card (LocalEdge L α π) ≤ P^2) :
    Fintype.card (sourceFiber α π a) ≤ P := by
  have h := source_degree_sq_le_edges (π := π) ha
  nlinarith
end ThreeSum.TernaryCoverRegularity
