-- Prove2me | solution 1 for SafetyLivenessDecomposition.slice_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:14.8015+00:00
-- url     : https://prove2.me/submissions/b6aec192-05df-4629-bd1c-ce8995f49332

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
theorem _root_.solution (α : FinWord T) (β : InfWord T) :
    (α.append β).slice α.length = α := by
  have hfun : (fun i : Fin α.length => (α.append β) i) = fun i : Fin α.length => α[i] := by
    funext i; simp [FinWord.append, i.2]
  simp [InfWord.slice, hfun]
end SafetyLivenessDecomposition
