-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.isFullConstantField_iff_algebraicClosure_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:49.425846+00:00
-- url     : https://prove2.me/submissions/09b4a61b-7f11-4840-86af-b2896b70d9c6

import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_FullConstantField

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped RatFunc
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (k F : Type*) [Field k] [Field F] [Algebra k F] :
    IsFullConstantField k F ↔ algebraicClosure k F = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨c, rfl⟩ := h.algebraic_mem x (mem_algebraicClosure_iff.mp hx)
    exact (⊥ : IntermediateField k F).algebraMap_mem c
  · intro h
    refine ⟨fun x hx => ?_⟩
    have hxb : x ∈ (⊥ : IntermediateField k F) :=
      h ▸ mem_algebraicClosure_iff.mpr hx
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hxb
    exact ⟨c, hc.symm⟩
end QEC.Coding.AlgebraicGeometry
