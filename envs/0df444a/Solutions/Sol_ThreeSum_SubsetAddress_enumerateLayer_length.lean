-- Prove2me | solution 1 for ThreeSum.SubsetAddress.enumerateLayer_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:20.010577+00:00
-- url     : https://prove2.me/submissions/a678bbdc-2d04-4c75-b8dd-08d308565b83

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
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution (L k : ℕ) : (enumerateLayer L k).length = L.choose k := by
  induction L generalizing k with
  | zero => cases k <;> simp [enumerateLayer]
  | succ L ih =>
      cases k with
      | zero => simp [enumerateLayer]
      | succ k =>
          by_cases hk : k + 1 ≤ L + 1
          · simp [enumerateLayer, hk, ih, Nat.choose_succ_succ, Nat.add_comm]
          · simp [enumerateLayer, hk, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]
end ThreeSum.SubsetAddress
