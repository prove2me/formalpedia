-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.boundary1_plaquetteBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:49:37.510578+00:00
-- url     : https://prove2.me/submissions/d79d1988-cd9b-4295-a32a-fcfc80343356

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Cellulation
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PeriodicCubical4
open scoped Classical
variable {L : Nat} [NeZero L]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution (p : Plaquette L) :
    boundary1 (plaquetteBoundary p) = 0 := by
  rcases p with ⟨x, p⟩
  cases p <;>
    simp [boundary1, plaquetteBoundary, linkBoundary, shift_commute,
      add_left_comm, add_comm]
end QEC.Coding.PeriodicCubical4
