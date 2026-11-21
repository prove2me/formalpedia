-- Prove2me | solution 1 for SafetyLivenessDecomposition.append_slice_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:15.282179+00:00
-- url     : https://prove2.me/submissions/74c39ddb-f65b-4c0b-8f1f-5bba70ec7774

module
public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.ToDual
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Finiteness.Attr
public import Definitions.Def_LeanPool_LeanModelChecking_SafetyLivenessDecomposition
public import Theorems.Thm_SafetyLivenessDecomposition_slice_length
public import Theorems.Thm_SafetyLivenessDecomposition_slice_get
attribute [local simp] SafetyLivenessDecomposition.slice_length
attribute [local simp] SafetyLivenessDecomposition.slice_get

set_option autoImplicit true
@[expose] public section
public section
open SafetyLivenessDecomposition
variable {T : Type u}
namespace SafetyLivenessDecomposition
theorem _root_.solution (σ : InfWord T) (n : ℕ) :
    (σ.slice n).append (fun k => σ (k + n)) = σ := by
  funext k
  by_cases hk : k < n
  · simp [FinWord.append, hk, slice_length]
  · have hle : n ≤ k := Nat.le_of_not_lt hk
    simp [FinWord.append, hk, slice_length, Nat.sub_add_cancel hle]
end SafetyLivenessDecomposition
