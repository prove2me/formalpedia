-- Prove2me | solution 2 for QEC.Semantics.Qubit.localXSupport_localZSupport_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:58:12.785921+00:00
-- url     : https://prove2.me/submissions/f638fdda-f740-469d-bb9f-2704e27f321a

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
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
theorem _root_.solution (xSupport zSupport : Finset ι)
    (ψ : QubitRegister ι) (bits : Bitstring ι) :
    (localXSupport xSupport * localZSupport zSupport) ψ bits =
      zSupportPhase zSupport (flipSupport xSupport bits) *
        ψ (flipSupport xSupport bits) := by
  simp [Module.End.mul_apply]
end QEC.Semantics.Qubit
