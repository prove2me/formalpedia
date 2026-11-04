-- Prove2me | solution 1 for ThreeSum.TernaryCoverOutputCap.choiceCode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:59.915471+00:00
-- url     : https://prove2.me/submissions/94141390-5dd4-405e-9d9f-368ff41692fa

import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data
import Theorems.Thm_ThreeSum_TernaryCoverLocal_endpoint_injective


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverOutputCap
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}
namespace ThreeSum.TernaryCoverOutputCap
theorem _root_.solution (α π : DigitType) (q : TritWord L) :
    Function.Injective (choiceCode (α := α) (π := π) (q := q)) := by
  intro e f h
  have hl : left e.val = left f.val := by
    funext i
    apply Fin.ext
    exact congrArg (fun z : Fin ((q i).val+1) => z.val) (congrFun h i)
  have hr : right e.val = right f.val := by
    funext i
    apply Fin.ext
    have hs := (edge_data e.val).2.2.2 i
    have ht := (edge_data f.val).2.2.2 i
    rw [e.property] at hs
    rw [f.property] at ht
    rw [hl] at hs
    omega
  apply Subtype.ext
  exact endpoint_injective α π (Prod.ext hl hr)
end ThreeSum.TernaryCoverOutputCap
