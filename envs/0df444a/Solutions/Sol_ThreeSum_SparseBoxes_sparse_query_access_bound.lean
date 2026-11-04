-- Prove2me | solution 1 for ThreeSum.SparseBoxes.sparse_query_access_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:49:51.780205+00:00
-- url     : https://prove2.me/submissions/854ec378-6dce-4489-83d4-e6acdc2e509f

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
import Theorems.Thm_ThreeSum_SparseBoxes_mem_records
import Theorems.Thm_ThreeSum_SparseBoxes_records_card_bound
import Definitions.Def_WeightedCache3SUM_Alias_110f593934b92a01
namespace ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
private theorem explicitLeaves_card_le_records (q : Finset α) (t : ℕ) :
    (explicitLeaves q t).card ≤ (records q t).card := by
  apply Finset.card_le_card_of_injOn
    (fun leaf => (⟨q \ leaf, 0⟩ : Sigma (fun _ : Finset α => ℕ)))
  · intro leaf hl
    obtain ⟨hlq, hsmall⟩ := (mem_explicitLeaves q leaf t).mp hl
    exact (mem_records q (q \ leaf) t 0).mpr
      ⟨Finset.sdiff_subset, Nat.le_of_lt hsmall, Nat.zero_le _⟩
  · intro a ha b hb he
    have hqa := ((mem_explicitLeaves q a t).mp ha).1
    have hqb := ((mem_explicitLeaves q b t).mp hb).1
    have hc : q \ a = q \ b := congrArg (fun r : Sigma (fun _ : Finset α => ℕ) => r.1) he
    calc
      a = q \ (q \ a) := (Finset.sdiff_sdiff_eq_self hqa).symm
      _ = q \ (q \ b) := congrArg (fun s => q \ s) hc
      _ = b := Finset.sdiff_sdiff_eq_self hqb
end ThreeSum.SparseBoxes
set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (q : Finset α) (t : ℕ) (ht : t ≤ q.card / 2) :
    (explicitLeaves q t).card + (q.powersetCard t).card ≤
      ((q.card + 1) ^ 2 + 1) * q.card.choose t := by
  have hsmall := (explicitLeaves_card_le_records q t).trans (records_card_bound q t ht)
  rw [Finset.card_powersetCard]
  calc
    _ ≤ (q.card + 1) ^ 2 * q.card.choose t + q.card.choose t :=
      Nat.add_le_add_right hsmall _
    _ = _ := by rw [Nat.add_mul, one_mul]
end ThreeSum.SparseBoxes
