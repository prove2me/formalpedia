-- Prove2me | solution 1 for Parikh.Component.denotation_eq_vadd_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:47:58.273853+00:00
-- url     : https://prove2.me/submissions/882b3d32-56db-45bb-86ff-b42bb16f1aab

module
public import Mathlib.Computability.Language
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Definitions.Def_LeanPool_Parikh_Counting

set_option autoImplicit true
@[expose] public section
public section
open scoped Pointwise
open Parikh
namespace Parikh
namespace Component
theorem _root_.solution {T : Type*} (c : Component T) :
    c.denotation = c.base +ᵥ
      (AddSubmonoid.closure (Set.range c.periods.get) : Set (Vector T)) := by
  ext x
  simp only [Component.denotation, Set.mem_ofPred_eq, Set.mem_vadd_set,
    SetLike.mem_coe, vadd_eq_add, AddSubmonoid.mem_closure_range_iff_of_fintype]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, rfl⟩
end Component
end Parikh
