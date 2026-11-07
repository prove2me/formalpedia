-- Prove2me | solution 1 for QEC.Distillation.EncodedCode.ImplementsLogicalGate.maps_codeCarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:59:46.777245+00:00
-- url     : https://prove2.me/submissions/3db2a187-2894-4877-a947-2964aed49560

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Theorems.Thm_QEC_Distillation_EncodedCode_exists_encode_eq_of_mem

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
    (h : E.ImplementsLogicalGate physical logical) {x : Physical}
    (hx : x ∈ E.code.carrier) :
    physical x ∈ E.code.carrier := by
  obtain ⟨psi, rfl⟩ := E.exists_encode_eq_of_mem hx
  rw [h psi]
  exact E.encode_mem (logical psi)
end QEC.Distillation.EncodedCode.ImplementsLogicalGate
