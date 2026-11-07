-- Prove2me | solution 1 for QEC.Distillation.EncodedCode.ImplementsLogicalGate.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:23:02.483899+00:00
-- url     : https://prove2.me/submissions/6766cde2-2c8c-430c-8b8e-c217025ba38e

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Distillation
open Semantics
variable {Logical Physical Site : Type u}
variable [NormedAddCommGroup Logical] [InnerProductSpace Complex Logical]
variable [FiniteQuantumSystem Logical]
variable [NormedAddCommGroup Physical] [InnerProductSpace Complex Physical]
variable [FiniteQuantumSystem Physical]
open QEC.Distillation.EncodedCode
open QEC.Distillation.EncodedCode.ImplementsLogicalGate
namespace QEC.Distillation.EncodedCode.ImplementsLogicalGate
theorem _root_.solution (E : EncodedCode Logical Physical)
    {physical : UnitaryTransport Physical Physical}
    {logical : UnitaryTransport Logical Logical}
    (h : E.ImplementsLogicalGate physical logical) :
    E.ImplementsLogicalGate physical.symm logical.symm := by
  intro psi
  have hpsi := congrArg physical.toLinearEquiv.symm (h (logical.symm psi))
  simpa [UnitaryTransport.symm] using hpsi.symm
end QEC.Distillation.EncodedCode.ImplementsLogicalGate
