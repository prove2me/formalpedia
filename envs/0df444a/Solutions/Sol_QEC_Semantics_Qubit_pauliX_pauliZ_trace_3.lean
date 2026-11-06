-- Prove2me | solution 3 for QEC.Semantics.Qubit.pauliX_pauliZ_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:52:10.722226+00:00
-- url     : https://prove2.me/submissions/bea5a631-1dd6-47b6-a8f6-d81edf4e9dd6

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_pauliX_pauliZ
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
    LinearMap.trace Complex QubitSpace (pauliX * pauliZ) = 0 := by
  rw [pauliX_pauliZ]
  simp [pauliY_trace]
end QEC.Semantics.Qubit
