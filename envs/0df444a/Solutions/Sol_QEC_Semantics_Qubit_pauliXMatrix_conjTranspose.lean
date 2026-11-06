-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliXMatrix_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:41:14.608238+00:00
-- url     : https://prove2.me/submissions/b77c6260-e7bf-4b36-8c50-e510f9c06ee4

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
namespace QEC.Semantics.Qubit
theorem _root_.solution : pauliXMatrix.conjTranspose = pauliXMatrix := by
  ext row col
  change star (pauliXMatrix col row) = pauliXMatrix row col
  fin_cases row <;> fin_cases col <;> simp [pauliXMatrix, flipBit]
end QEC.Semantics.Qubit
