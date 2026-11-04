-- Prove2me | solution 1 for ThreeSum.SubsetAddress.mem_enumerateLayer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:26.930116+00:00
-- url     : https://prove2.me/submissions/cafca770-dd0a-4c21-98c3-cd16a0e4c8f3

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Embedding
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_le_width
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_succ_low
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_succ_high
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution (L k m : ℕ) : m ∈ enumerateLayer L k ↔ IsMask L k m := by
  induction L generalizing k m with
  | zero =>
      cases k with
      | zero => simp [enumerateLayer]
      | succ k => simp [enumerateLayer, IsMask, weight]
  | succ L ih =>
      cases k with
      | zero => simp [enumerateLayer]
      | succ k =>
          by_cases hk : k + 1 ≤ L + 1
          · simp only [enumerateLayer, if_pos hk, List.mem_append, List.mem_map, ih]
            constructor
            · rintro (hm | ⟨a, ha, rfl⟩)
              · exact hm.succ_low
              · exact ha.succ_high
            · intro hm
              by_cases hc : m < 2 ^ L
              · exact Or.inl (hm.low hc)
              · right
                refine ⟨m - 2 ^ L, ?_, by omega⟩
                simpa only [Nat.add_sub_cancel] using (hm.high (Nat.le_of_not_gt hc)).2
          · have hn : ¬IsMask (L + 1) (k + 1) m := fun hm => hk hm.le_width
            simp [enumerateLayer, hk, hn]
end ThreeSum.SubsetAddress
