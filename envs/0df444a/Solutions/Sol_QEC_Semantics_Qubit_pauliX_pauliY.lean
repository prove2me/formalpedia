-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliX_pauliY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:38:46.628557+00:00
-- url     : https://prove2.me/submissions/533e3821-bac5-4b00-995e-937f346921a6

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
theorem _root_.solution : pauliX * pauliY = Complex.I • pauliZ := by
  ext ψ b
  fin_cases b <;> simp [Module.End.mul_apply]
end QEC.Semantics.Qubit
