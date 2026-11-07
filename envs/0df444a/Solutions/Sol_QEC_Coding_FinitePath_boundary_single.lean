-- Prove2me | solution 1 for QEC.Coding.FinitePath.boundary_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:08:49.606146+00:00
-- url     : https://prove2.me/submissions/f8f13b13-a4b2-4bf8-87c8-129a1ba89a2d

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_FinitePath
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FinitePath
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
omit [Fintype F] [DecidableEq F]
namespace QEC.Coding.FinitePath
theorem _root_.solution {n : Nat} (i : Fin (n + 1)) :
    boundary (F := F) (Pi.single i 1) = vertexCoboundary (F := F) i := by
  classical
  ext j
  unfold boundary
  dsimp
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hne
    rw [Pi.single_eq_of_ne hne, zero_mul]
  · simp
end QEC.Coding.FinitePath
