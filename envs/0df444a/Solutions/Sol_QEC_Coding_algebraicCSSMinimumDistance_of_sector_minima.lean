-- Prove2me | solution 1 for QEC.Coding.algebraicCSSMinimumDistance_of_sector_minima
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:14:28.850663+00:00
-- url     : https://prove2.me/submissions/11420ffd-011d-471d-9079-ee70fb33e2ef

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
namespace QEC.Coding
theorem _root_.solution
    {F : Type u} {ι : Type v} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {xCode zCode : LinearCode F ι} {dX dZ : Nat}
    (hX : PureXLogicalMinimumDistance xCode zCode dX)
    (hZ : PureZLogicalMinimumDistance xCode zCode dZ) :
    AlgebraicCSSMinimumDistance xCode zCode (min dX dZ) := by
  change RelativeMinimumDistance zCode.dual xCode dX at hX
  change RelativeMinimumDistance xCode.dual zCode dZ at hZ
  rcases hX with ⟨x, hxDual, hxTrivial, hxWeight, hxLeast⟩
  rcases hZ with ⟨z, hzDual, hzTrivial, hzWeight, hzLeast⟩
  unfold AlgebraicCSSMinimumDistance
  rcases le_total dX dZ with hXZ | hZX
  · refine ⟨x, Or.inl ⟨hxDual, hxTrivial⟩, ?_, ?_⟩
    · simpa [Nat.min_eq_left hXZ] using hxWeight
    · intro y hy
      rw [Nat.min_eq_left hXZ]
      rcases hy with hyX | hyZ
      · exact hxLeast y hyX.1 hyX.2
      · exact hXZ.trans (hzLeast y hyZ.1 hyZ.2)
  · refine ⟨z, Or.inr ⟨hzDual, hzTrivial⟩, ?_, ?_⟩
    · simpa [Nat.min_eq_right hZX] using hzWeight
    · intro y hy
      rw [Nat.min_eq_right hZX]
      rcases hy with hyX | hyZ
      · exact hZX.trans (hxLeast y hyX.1 hyX.2)
      · exact hzLeast y hyZ.1 hyZ.2
end QEC.Coding
