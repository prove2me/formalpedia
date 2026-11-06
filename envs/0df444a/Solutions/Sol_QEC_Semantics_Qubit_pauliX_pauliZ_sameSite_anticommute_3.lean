-- Prove2me | solution 3 for QEC.Semantics.Qubit.pauliX_pauliZ_sameSite_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:51:42.0377+00:00
-- url     : https://prove2.me/submissions/68d9d934-1b45-4e42-ae2c-db533169e929

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
theorem _root_.solution :
    pauliX * pauliZ = -(pauliZ * pauliX) := by
  ext ψ b
  simp [Module.End.mul_apply]
end QEC.Semantics.Qubit
