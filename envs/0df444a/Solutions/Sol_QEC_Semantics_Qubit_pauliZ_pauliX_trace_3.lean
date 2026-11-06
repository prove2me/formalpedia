-- Prove2me | solution 3 for QEC.Semantics.Qubit.pauliZ_pauliX_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:56:47.605431+00:00
-- url     : https://prove2.me/submissions/615d1b66-174f-45d4-a066-092dc0efb87f

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_pauliX
import Theorems.Thm_QEC_Semantics_Qubit_pauliY_trace
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
    LinearMap.trace Complex QubitSpace (pauliZ * pauliX) = 0 := by
  rw [pauliZ_pauliX]
  simp [pauliY_trace]
end QEC.Semantics.Qubit
