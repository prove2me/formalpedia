-- Prove2me | solution 1 for QEC.Semantics.Qubit.localX_localZ_commute_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:41:38.003182+00:00
-- url     : https://prove2.me/submissions/05d2cb07-d8d7-45d1-ae68-f89f13b8190e

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_flipAt_apply_ne
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
theorem _root_.solution {i j : ι} (h : i ≠ j) :
    localX i * localZ j = localZ j * localX i := by
  ext ψ bits
  have hj : j ≠ i := h.symm
  simp [Module.End.mul_apply, flipAt_apply_ne bits hj]
end QEC.Semantics.Qubit
