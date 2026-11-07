-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.translateCoord_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:50.955181+00:00
-- url     : https://prove2.me/submissions/5ba6ebeb-3313-416e-b58c-93a5084456b1

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
theorem _root_.solution {L : Nat} (u v x : Coord L) :
    translateCoord u (translateCoord v x) = translateCoord (u + v) x := by
  simp [translateCoord, add_comm, add_left_comm]
end QEC.Coding.PeriodicCubical4
