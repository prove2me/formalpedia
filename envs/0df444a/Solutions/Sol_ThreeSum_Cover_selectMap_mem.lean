-- Prove2me | solution 1 for ThreeSum.Cover.selectMap_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:13.49733+00:00
-- url     : https://prove2.me/submissions/f6b45b62-e341-41ae-8912-b0c62f81805b

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
theorem _root_.solution (maps : List Ω) (hne : maps ≠ [])
    (covers : Ω → U → Prop) [DecidableRel covers] (targets : Finset U) :
    selectMap maps covers targets ∈ maps := by
  unfold selectMap
  cases h : maps.argmax (fun ω => (targets.filter (covers ω)).card) with
  | none => exact False.elim (hne (List.argmax_eq_none.mp h))
  | some ω =>
    simp only [Option.getD_some]
    exact List.argmax_mem (f := fun ω => (targets.filter (covers ω)).card)
      (by simpa only [Option.mem_def] using h)
end ThreeSum.Cover
