-- Prove2me | solution 1 for ThreeSum.TernaryCoverOutputCap.source_degree_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:12.033443+00:00
-- url     : https://prove2.me/submissions/ee6175aa-2116-4970-80df-023c2b7317ac

import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Theorems.Thm_ThreeSum_TernaryCoverOutputCap_edges_card_le
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_source_degree_le_prime


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverOutputCap
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}
namespace ThreeSum.TernaryCoverOutputCap
theorem _root_.solution {α π : DigitType} {a : TritWord L} (ha : HasType a α)
    (P : ℕ) (hP : (vertices L π).card * (2^(π 1)*3^(π 2)) ≤ P^2) :
    Fintype.card (TernaryCoverRegularity.sourceFiber α π a) ≤ P :=
  TernaryCoverRegularity.source_degree_le_prime ha P ((edges_card_le α π).trans hP)
end ThreeSum.TernaryCoverOutputCap
