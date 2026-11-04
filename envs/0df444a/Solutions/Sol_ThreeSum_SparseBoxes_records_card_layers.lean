-- Prove2me | solution 1 for ThreeSum.SparseBoxes.records_card_layers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:45:15.73974+00:00
-- url     : https://prove2.me/submissions/44ca9428-3ed0-4f1f-889f-473c0e295a15

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
import Theorems.Thm_ThreeSum_SparseBoxes_records_card

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (ambient : Finset α) (cut : ℕ) :
    (records ambient cut).card =
      ∑ j ∈ Finset.range (ambient.card + 1),
        if j ≤ cut then (j + 1) * ambient.card.choose j else 0 := by
  rw [records_card, Finset.sum_filter, Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro j hj
  have hconst :
      (∑ flags ∈ ambient.powersetCard j,
        if flags.card ≤ cut then flags.card + 1 else 0) =
      ∑ _flags ∈ ambient.powersetCard j, if j ≤ cut then j + 1 else 0 := by
    apply Finset.sum_congr rfl
    intro flags hf
    rw [(Finset.mem_powersetCard.mp hf).2]
  rw [hconst]
  by_cases hjc : j ≤ cut
  · simp [hjc, Nat.mul_comm]
  · simp [hjc]
end ThreeSum.SparseBoxes
