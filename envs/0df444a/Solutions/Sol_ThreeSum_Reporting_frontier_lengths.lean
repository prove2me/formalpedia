-- Prove2me | solution 1 for ThreeSum.Reporting.frontier_lengths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:28.109417+00:00
-- url     : https://prove2.me/submissions/c31a5315-c6dc-4abe-9f23-aca32c93e27c

import Definitions.Def_Submission_ThreeSum_Subset
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Definitions.Def_Submission_ThreeSum_Reporting

set_option autoImplicit false
open ThreeSum ThreeSum.Reporting
open Finset
open scoped BigOperators
variable {ι α : Type*} [DecidableEq α]
namespace ThreeSum.Reporting
theorem _root_.solution (children : ℕ → List α) (query : ℕ → List α → ℕ)
    (k : ℕ) : ∀ pre ∈ frontier children query k, pre.length = k := by
  induction k with
  | zero =>
      intro pre hp
      simp only [frontier] at hp
      split at hp
      · simpa using congrArg List.length (List.mem_singleton.mp hp)
      · cases hp
  | succ k ih =>
      intro pre hp
      obtain ⟨parent, hparent, hpre⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hpre
      simp [ih parent hparent]
end ThreeSum.Reporting
