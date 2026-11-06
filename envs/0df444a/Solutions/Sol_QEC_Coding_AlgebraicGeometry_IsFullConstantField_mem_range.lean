-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.IsFullConstantField.mem_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:01:38.339878+00:00
-- url     : https://prove2.me/submissions/bf995a89-a0b1-436e-b7cf-3139b6cbfade

import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_FullConstantField

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped RatFunc
open QEC.Coding.AlgebraicGeometry.IsFullConstantField
variable (k F : Type*) [Field k] [Field F] [Algebra k F] [IsFullConstantField k F]
namespace QEC.Coding.AlgebraicGeometry.IsFullConstantField
theorem _root_.solution {x : F} (hx : IsAlgebraic k x) :
    x ∈ Set.range (algebraMap k F) := by
  obtain ⟨c, hc⟩ := IsFullConstantField.algebraic_mem (k := k) (F := F) x hx
  exact ⟨c, hc.symm⟩
end QEC.Coding.AlgebraicGeometry.IsFullConstantField
