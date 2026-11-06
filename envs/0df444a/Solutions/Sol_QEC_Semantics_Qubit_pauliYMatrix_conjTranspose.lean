-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliYMatrix_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:56:25.070142+00:00
-- url     : https://prove2.me/submissions/429b16a3-2a54-4cdd-b7a5-14aa081dbc6d

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
theorem _root_.solution : pauliYMatrix.conjTranspose = pauliYMatrix := by
  ext row col
  change star (pauliYMatrix col row) = pauliYMatrix row col
  fin_cases row <;> fin_cases col <;> simp [pauliYMatrix]
end QEC.Semantics.Qubit
