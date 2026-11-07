-- Prove2me | solution 1 for QEC.Distillation.EncodedCode.exists_encode_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:58:27.366987+00:00
-- url     : https://prove2.me/submissions/546d0d02-c274-40a9-aee2-17dcae048ed2

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
namespace QEC.Distillation.EncodedCode
theorem _root_.solution (E : EncodedCode Logical Physical) {x : Physical}
    (hx : x ∈ E.code.carrier) :
    ∃ psi : Logical, E.encode psi = x := by
  let xInCode : E.code.carrier := ⟨x, hx⟩
  refine ⟨E.encoding.symm xInCode, ?_⟩
  simp [encode, xInCode]
end QEC.Distillation.EncodedCode
