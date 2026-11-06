-- Prove2me | solution 2 for QEC.Semantics.Qubit.localZ_localZ_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:57:15.398468+00:00
-- url     : https://prove2.me/submissions/0c7ef816-a230-41f7-9b2f-ff3dd0291c3e

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
theorem _root_.solution (i j : ι) :
    localZ i * localZ j = localZ j * localZ i := by
  ext ψ bits
  simp [Module.End.mul_apply, mul_left_comm]
end QEC.Semantics.Qubit
