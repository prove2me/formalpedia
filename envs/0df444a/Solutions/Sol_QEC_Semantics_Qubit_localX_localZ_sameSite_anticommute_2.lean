-- Prove2me | solution 2 for QEC.Semantics.Qubit.localX_localZ_sameSite_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:57:02.154363+00:00
-- url     : https://prove2.me/submissions/1acf0fbd-7de1-4d84-8106-e2e53e0d6996

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
theorem _root_.solution (i : ι) :
    localX i * localZ i = -(localZ i * localX i) := by
  ext ψ bits
  simp [Module.End.mul_apply]
end QEC.Semantics.Qubit
