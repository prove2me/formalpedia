-- Prove2me | solution 1 for ThreeSum.Subset.block_refinement_conservation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:24.821827+00:00
-- url     : https://prove2.me/submissions/d96f30b2-872c-431c-bfb9-23d4950491b1

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Subset
import Theorems.Thm_ThreeSum_Subset_fiberMass_conservation

set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.Subset
theorem _root_.solution
    (completions : Finset (Finset α)) (block : Finset α)
    (weight : Finset α → ℕ) :
    (∑ child ∈ block.powerset,
      fiberMass completions (fun s => s ∩ block) weight child) =
      ∑ s ∈ completions, weight s := by
  apply fiberMass_conservation
  intro s hs
  exact Finset.mem_powerset.mpr Finset.inter_subset_right
end ThreeSum.Subset
