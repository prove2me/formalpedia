-- Prove2me | solution 1 for ThreeSum.Subset.balanced_block_refinement_conservation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:25.807956+00:00
-- url     : https://prove2.me/submissions/5f77bb31-2dae-48da-9e8b-1e34b307b828

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
    (completions : Finset (Finset α)) (block : Finset α) (h : ℕ)
    (weight : Finset α → ℕ)
    (hbalanced : ∀ s ∈ completions, (s ∩ block).card = h) :
    (∑ child ∈ block.powersetCard h,
      fiberMass completions (fun s => s ∩ block) weight child) =
      ∑ s ∈ completions, weight s := by
  apply fiberMass_conservation
  intro s hs
  exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hbalanced s hs⟩
end ThreeSum.Subset
