-- Prove2me | solution 1 for ThreeSum.Cover.greedyState_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:30.308612+00:00
-- url     : https://prove2.me/submissions/39c293d7-aa46-48d9-bd65-d6f0d2bde91b

import Definitions.Def_Submission_ThreeSum_Cover
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring
import Aesop
import Definitions.Def_Submission_ThreeSum_Greedy
import Theorems.Thm_ThreeSum_Cover_greedyState_spec

set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators
variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]
namespace ThreeSum.Cover
theorem _root_.solution (maps : List Ω) (covers : Ω → U → Prop)
    [DecidableRel covers] (targets : Finset U) (t : ℕ) :
    greedyState maps covers targets t ⊆ targets := by
  intro u hu
  exact ((greedyState_spec maps covers targets t u).mp hu).1
end ThreeSum.Cover
