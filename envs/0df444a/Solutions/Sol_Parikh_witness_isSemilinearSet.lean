-- Prove2me | solution 1 for Parikh.witness_isSemilinearSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:15.123174+00:00
-- url     : https://prove2.me/submissions/fae05046-2536-40e2-87ee-351a4e1e934e

module
public import Mathlib.Computability.Language
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Definitions.Def_LeanPool_Parikh_Counting
public import Theorems.Thm_Parikh_component_isLinearSet

set_option autoImplicit true
@[expose] public section
public section
open scoped Pointwise
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} (W : Witness T) :
    IsSemilinearSet W.denotation := by
  classical
  have h : W.denotation = ⋃ c ∈ W.toFinset, c.denotation := by
    ext v
    simp [Witness.denotation]
  rw [h]
  exact IsSemilinearSet.biUnion_finset fun c _ =>
    (component_isLinearSet c).isSemilinearSet
end Parikh
