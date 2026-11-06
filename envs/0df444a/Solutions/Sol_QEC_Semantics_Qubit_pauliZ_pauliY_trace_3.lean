-- Prove2me | solution 3 for QEC.Semantics.Qubit.pauliZ_pauliY_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:56:53.051946+00:00
-- url     : https://prove2.me/submissions/42208d34-0007-4e98-a499-df75f690431b

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_pauliY
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
    LinearMap.trace Complex QubitSpace (pauliZ * pauliY) = 0 := by
  rw [pauliZ_pauliY]
  simp [pauliX_trace]
end QEC.Semantics.Qubit
