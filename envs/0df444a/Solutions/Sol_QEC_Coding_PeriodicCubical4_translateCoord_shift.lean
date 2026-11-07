-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.translateCoord_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:52.040243+00:00
-- url     : https://prove2.me/submissions/bcf9c0b3-c211-4034-b040-5c8c57eefd6e

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
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution {L : Nat} (v x : Coord L) (a : Axis) :
    translateCoord v (shift x a) = shift (translateCoord v x) a := by
  simp [translateCoord, shift, add_comm, add_left_comm]
end QEC.Coding.PeriodicCubical4
