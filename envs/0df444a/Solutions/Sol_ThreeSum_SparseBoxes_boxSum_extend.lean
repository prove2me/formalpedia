-- Prove2me | solution 1 for ThreeSum.SparseBoxes.boxSum_extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:35:00.368478+00:00
-- url     : https://prove2.me/submissions/6bf7af92-b0c1-4df9-a2c6-55a1a57ce022

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
theorem _root_.solution (ambient flags free : Finset α) (weight : Finset α → ℤ)
    (hf : flags ⊆ ambient) :
    boxSum flags free weight =
      ∑ leaf ∈ ambient.powerset,
        if BoxMember flags free leaf then weight leaf else 0 := by
  unfold boxSum
  calc
    _ = ∑ leaf ∈ flags.powerset,
          if BoxMember flags free leaf then weight leaf else 0 := by
      apply Finset.sum_congr rfl
      intro leaf hl
      simp only [BoxMember, Finset.mem_powerset.mp hl, true_and]
    _ = _ := by
      apply Finset.sum_subset
      · intro leaf hl
        exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hl).trans hf)
      · intro leaf hl hnl
        have hn : ¬ BoxMember flags free leaf := by
          intro h
          exact hnl (Finset.mem_powerset.mpr h.1)
        simp only [hn, ite_false]
end ThreeSum.SparseBoxes
