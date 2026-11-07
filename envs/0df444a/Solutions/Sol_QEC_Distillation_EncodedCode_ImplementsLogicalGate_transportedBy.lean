-- Prove2me | solution 1 for QEC.Distillation.EncodedCode.ImplementsLogicalGate.transportedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:16:45.456223+00:00
-- url     : https://prove2.me/submissions/2b7de7c2-9fff-4d87-8f4d-bf11e7fa589e

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_maps_codeCarrier
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
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
    QuantumCode.TransportedBy physical E.code E.code := by
  intro x
  constructor
  · exact h.maps_codeCarrier
  · intro hx
    have hback := maps_codeCarrier E (symm E h) hx
    simpa [UnitaryTransport.symm] using hback
end QEC.Distillation.EncodedCode.ImplementsLogicalGate
