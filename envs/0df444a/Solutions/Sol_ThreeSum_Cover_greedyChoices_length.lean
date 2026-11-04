-- Prove2me | solution 1 for ThreeSum.Cover.greedyChoices_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:15.625572+00:00
-- url     : https://prove2.me/submissions/a211298d-e99e-4b56-90ed-4d0e17f63484

import Definitions.Def_Submission_ThreeSum_Cover
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring
import Aesop
import Definitions.Def_Submission_ThreeSum_Greedy

set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators
variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]
namespace ThreeSum.Cover
theorem _root_.solution (maps : List Ω) (covers : Ω → U → Prop)
    [DecidableRel covers] (targets : Finset U) (t : ℕ) :
    (greedyChoices maps covers targets t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [greedyChoices, ih]
end ThreeSum.Cover
