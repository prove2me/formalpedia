-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliZMatrix_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:56:59.565646+00:00
-- url     : https://prove2.me/submissions/d99d54c7-1283-4279-a7c3-7c373af92296

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
theorem _root_.solution : pauliZMatrix.conjTranspose = pauliZMatrix := by
  ext row col
  change star (pauliZMatrix col row) = pauliZMatrix row col
  by_cases h : row = col
  · subst col
    simp [pauliZMatrix]
  · have hc : ¬ col = row := fun hc => h hc.symm
    simp [pauliZMatrix, h, hc]
end QEC.Semantics.Qubit
