-- Prove2me | solution 1 for ThreeSum.SparseBoxes.mem_explicitLeaves_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:35:01.666796+00:00
-- url     : https://prove2.me/submissions/3313a84d-072e-498a-ad42-e4f765e5812f

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SparseBoxes

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (q leaf : Finset α) (t : ℕ) :
    leaf ∈ explicitLeaves q t ↔ leaf ⊆ q ∧ (q \ leaf).card < t := by
  constructor
  · intro hl
    obtain ⟨missing, hm, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨hmq, hmc⟩ := Finset.mem_powersetCard.mp hmj
    refine ⟨Finset.sdiff_subset, ?_⟩
    rw [Finset.sdiff_sdiff_eq_self hmq, hmc]
    exact Finset.mem_range.mp hj
  · rintro ⟨hlq, hsmall⟩
    apply Finset.mem_image.mpr
    refine ⟨q \ leaf, ?_, Finset.sdiff_sdiff_eq_self hlq⟩
    exact Finset.mem_biUnion.mpr
      ⟨(q \ leaf).card, Finset.mem_range.mpr hsmall,
        Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset, rfl⟩⟩
end ThreeSum.SparseBoxes
