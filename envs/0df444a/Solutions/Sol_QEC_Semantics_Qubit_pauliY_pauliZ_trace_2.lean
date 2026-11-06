-- Prove2me | solution 2 for QEC.Semantics.Qubit.pauliY_pauliZ_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:55:35.262541+00:00
-- url     : https://prove2.me/submissions/77210d20-5e6e-4d9a-9883-0d4c52dd94c7

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_pauliY_pauliZ
import Theorems.Thm_QEC_Semantics_Qubit_pauliX_trace
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
    LinearMap.trace Complex QubitSpace (pauliY * pauliZ) = 0 := by
  rw [pauliY_pauliZ]
  simp [pauliX_trace]
end QEC.Semantics.Qubit
