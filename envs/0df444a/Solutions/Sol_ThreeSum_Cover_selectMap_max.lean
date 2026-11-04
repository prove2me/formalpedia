-- Prove2me | solution 1 for ThreeSum.Cover.selectMap_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:14.561719+00:00
-- url     : https://prove2.me/submissions/338e0fa8-fdd0-4b2c-b1f4-e09bb711c055

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
    [DecidableRel covers] (targets : Finset U) {ω : Ω} (hω : ω ∈ maps) :
    (targets.filter (covers ω)).card ≤
      (targets.filter (covers (selectMap maps covers targets))).card := by
  unfold selectMap
  cases h : maps.argmax (fun ω => (targets.filter (covers ω)).card) with
  | none => have := List.argmax_eq_none.mp h; simp_all
  | some v =>
    simp only [Option.getD_some]
    exact List.le_of_mem_argmax (f := fun ω => (targets.filter (covers ω)).card)
      hω (by simpa only [Option.mem_def] using h)
end ThreeSum.Cover
