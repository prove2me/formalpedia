-- Prove2me | solution 3 for QEC.Semantics.Qubit.pauliY_pauliX_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:52:47.862649+00:00
-- url     : https://prove2.me/submissions/a6d6208f-e935-45d2-86e1-f5963fef1384

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_pauliY_pauliX
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
    LinearMap.trace Complex QubitSpace (pauliY * pauliX) = 0 := by
  rw [pauliY_pauliX]
  simp [pauliZ_trace]
end QEC.Semantics.Qubit
