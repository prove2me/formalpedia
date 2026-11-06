-- Prove2me | solution 1 for QEC.Semantics.Qubit.localXSupport_localZSupport_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:58:27.208987+00:00
-- url     : https://prove2.me/submissions/df49c32b-a3b7-4c85-b3cf-c76bd592c648

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_zSupportPhase_flipSupport
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply

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
theorem _root_.solution (xSupport zSupport : Finset ι) :
    localXSupport xSupport * localZSupport zSupport =
      supportPhaseSign xSupport zSupport •
        (localZSupport zSupport * localXSupport xSupport) := by
  ext ψ bits
  simp [zSupportPhase_flipSupport, mul_assoc]
end QEC.Semantics.Qubit
