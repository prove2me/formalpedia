-- Prove2me | solution 1 for SafetyLivenessDecomposition.slice_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:45.254542+00:00
-- url     : https://prove2.me/submissions/e5f5ff52-8e06-421c-8fd6-dab329217cf1

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

set_option autoImplicit true
@[expose] public section
public section
open SafetyLivenessDecomposition
variable {T : Type u}
namespace SafetyLivenessDecomposition
theorem _root_.solution (σ : InfWord T) (n : ℕ) : (σ.slice n).length = n := by
  simp [InfWord.slice]
end SafetyLivenessDecomposition
