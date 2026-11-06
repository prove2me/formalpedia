-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliY_pauliZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:39:07.216007+00:00
-- url     : https://prove2.me/submissions/79c0096a-63af-4210-9442-4e4c39dcdb57

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
theorem _root_.solution : pauliY * pauliZ = Complex.I • pauliX := by
  ext ψ b
  fin_cases b <;> simp [Module.End.mul_apply]
end QEC.Semantics.Qubit
