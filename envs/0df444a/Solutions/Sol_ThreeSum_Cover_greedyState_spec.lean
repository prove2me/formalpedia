-- Prove2me | solution 1 for ThreeSum.Cover.greedyState_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:16.662214+00:00
-- url     : https://prove2.me/submissions/6880fd97-4465-4303-a144-838a6172c87e

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
    [DecidableRel covers] (targets : Finset U) (t : ℕ) (u : U) :
    u ∈ greedyState maps covers targets t ↔
      u ∈ targets ∧ ∀ ω ∈ greedyChoices maps covers targets t, ¬ covers ω u := by
  induction t with
  | zero => simp [greedyState, greedyChoices]
  | succ t ih =>
    simp only [greedyState, mem_filter, greedyChoices, List.mem_append, List.mem_singleton, ih]
    aesop
end ThreeSum.Cover
