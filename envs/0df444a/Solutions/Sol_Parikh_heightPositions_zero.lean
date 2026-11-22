-- Prove2me | solution 1 for Parikh.heightPositions_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:48:35.663324+00:00
-- url     : https://prove2.me/submissions/58bb35af-b8d0-4094-921d-1f9f14f62743

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport

set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution (b : ℕ) : heightPositions b 0 = 1 := by
  simp [heightPositions]
end Parikh
