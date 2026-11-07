-- Prove2me | solution 1 for QEC.Coding.KT19ReedSolomon.evaluationMap_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:14:57.005592+00:00
-- url     : https://prove2.me/submissions/a17811b1-c383-41c6-801e-c188a2a92bfe

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
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
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
namespace QEC.Coding.KT19ReedSolomon
theorem _root_.solution (p : Nat)
    (left right : Polynomial (ZMod p)) :
    evaluationMap p (left * right) =
      coordinatewiseProduct (evaluationMap p left) (evaluationMap p right) := by
  funext point
  simp [evaluationMap, coordinatewiseProduct]
end QEC.Coding.KT19ReedSolomon
