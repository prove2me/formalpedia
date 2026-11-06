-- Prove2me | solution 2 for QEC.Semantics.Qubit.localZ_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:57:00.890616+00:00
-- url     : https://prove2.me/submissions/c8465348-ade8-4e82-84ac-649387a5fc0a

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
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Qubit
theorem _root_.solution (i : ι) : localZ i * localZ i = 1 := by
  ext ψ bits
  simp only [Module.End.mul_apply, localZ_apply]
  rw [← mul_assoc, zPhase_sq, one_mul]
  rfl
end QEC.Semantics.Qubit
