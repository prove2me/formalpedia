-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliY_pauliX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:39:02.851943+00:00
-- url     : https://prove2.me/submissions/f227af18-88a2-4f80-af86-702f68479292

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
theorem _root_.solution : pauliY * pauliX = -Complex.I • pauliZ := by
  ext ψ b
  fin_cases b <;> simp [Module.End.mul_apply]
end QEC.Semantics.Qubit
