-- Prove2me | solution 1 for SafetyLivenessDecomposition.slice_get
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:17.692669+00:00
-- url     : https://prove2.me/submissions/5202f216-940e-4b40-b194-c8b4fe5c3e90

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
attribute [local simp] SafetyLivenessDecomposition.slice_length

set_option autoImplicit true
@[expose] public section
public section
open SafetyLivenessDecomposition
variable {T : Type u}
namespace SafetyLivenessDecomposition
theorem _root_.solution (σ : InfWord T) (n k : ℕ)
    (hk : k < (σ.slice n).length) :
    (σ.slice n)[k] = σ k := by
  simp [InfWord.slice]
end SafetyLivenessDecomposition
