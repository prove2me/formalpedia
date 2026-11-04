-- Prove2me | solution 1 for ThreeSum.SubsetAddress.enumerationWork_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:28.054865+00:00
-- url     : https://prove2.me/submissions/b5a441ef-ac88-49a3-9a38-e5725a897d67

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
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_length
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution (L k : ℕ) :
    enumerationWork L k ≤ (4 * L + 1) * L.choose k + 1 := by
  induction L generalizing k with
  | zero => cases k <;> simp [enumerationWork]
  | succ L ih =>
      cases k with
      | zero => simp [enumerationWork]
      | succ k =>
          by_cases hk : k + 1 ≤ L + 1
          · have hi := ih (k + 1)
            have hj := ih k
            have hp := Nat.choose_pos hk
            rw [Nat.choose_succ_succ] at hp
            simp only [enumerationWork, if_pos hk, enumerateLayer_length,
              Nat.choose_succ_succ]
            nlinarith
          · simp [enumerationWork, hk, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]
end ThreeSum.SubsetAddress
