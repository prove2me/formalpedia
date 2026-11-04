-- Prove2me | solution 1 for ThreeSum.Subset.partialZeta_forced_prefix_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:16.819589+00:00
-- url     : https://prove2.me/submissions/87b6d83d-30e8-4efa-8cc6-cfbf9a73d3c9

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

set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.Subset
theorem _root_.solution
    (f : Finset α → ℤ) (processed s₀ t : Finset α)
    (hs : Disjoint s₀ processed) (ht : t ⊆ processed) :
    partialZeta processed f (s₀ ∪ t) =
      ∑ x ∈ t.powerset, f (s₀ ∪ x) := by
  have hnot : ∀ x ∈ s₀, x ∉ processed := fun x hx hy =>
    Finset.disjoint_left.mp hs hx hy
  have hi : (s₀ ∪ t) ∩ processed = t := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    aesop
  have hd : (s₀ ∪ t) \ processed = s₀ := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx, hp⟩
      rcases hx with hxs | hxt
      · exact hxs
      · exact False.elim (hp (ht hxt))
    · intro hx
      exact ⟨Or.inl hx, hnot x hx⟩
  simp only [partialZeta, hi, hd]
end ThreeSum.Subset
