-- Prove2me | solution 2 for QEC.Semantics.Qubit.localZSupport_localXSupport_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:58:23.090977+00:00
-- url     : https://prove2.me/submissions/b7d8eea4-0ed4-4942-b307-16d6680837c1

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
    (localZSupport zSupport * localXSupport xSupport) ψ bits =
      zSupportPhase zSupport bits * ψ (flipSupport xSupport bits) := by
  simp [Module.End.mul_apply]
end QEC.Semantics.Qubit
