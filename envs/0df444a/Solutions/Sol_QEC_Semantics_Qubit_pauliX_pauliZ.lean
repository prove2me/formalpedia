-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliX_pauliZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:39:25.650804+00:00
-- url     : https://prove2.me/submissions/a8fd01a4-bd8b-47f7-a4ad-c95ad6d0f62b

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
theorem _root_.solution : pauliX * pauliZ = -Complex.I • pauliY := by
  ext ψ b
  fin_cases b <;> simp [Module.End.mul_apply] <;>
    rw [← mul_assoc, Complex.I_mul_I] <;> ring
end QEC.Semantics.Qubit
