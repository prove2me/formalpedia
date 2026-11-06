-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliZ_pauliY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:39:12.273272+00:00
-- url     : https://prove2.me/submissions/eb761fd8-d16e-4d73-9348-d16d87a1dc6c

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
theorem _root_.solution : pauliZ * pauliY = -Complex.I • pauliX := by
  ext ψ b
  fin_cases b <;> simp [Module.End.mul_apply]
end QEC.Semantics.Qubit
