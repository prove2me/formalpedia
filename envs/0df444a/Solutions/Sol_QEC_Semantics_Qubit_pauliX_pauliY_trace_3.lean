-- Prove2me | solution 3 for QEC.Semantics.Qubit.pauliX_pauliY_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:51:54.080205+00:00
-- url     : https://prove2.me/submissions/57fafc52-6db1-43f6-8ccf-eae80e3d6347

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_pauliX_pauliY
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_trace
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
theorem _root_.solution :
    LinearMap.trace Complex QubitSpace (pauliX * pauliY) = 0 := by
  rw [pauliX_pauliY]
  simp [pauliZ_trace]
end QEC.Semantics.Qubit
