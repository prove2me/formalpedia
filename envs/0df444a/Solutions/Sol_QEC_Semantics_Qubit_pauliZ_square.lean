-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliZ_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:41:14.159435+00:00
-- url     : https://prove2.me/submissions/9d08ffc2-8e37-41dc-b975-78a0d9588640

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
theorem _root_.solution : pauliZ * pauliZ = 1 := by
  ext ψ b
  simp only [Module.End.mul_apply, pauliZ_apply]
  rw [← mul_assoc, zPhase_sq, one_mul]
  rfl
end QEC.Semantics.Qubit
