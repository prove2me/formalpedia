-- Prove2me | solution 1 for QEC.Semantics.QuantumCode.projector_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:35:11.590311+00:00
-- url     : https://prove2.me/submissions/c4fe2d35-407b-4727-a130-df931fe7a1b0

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped ComplexOrder
noncomputable section
open QEC.Semantics.QuantumCode
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.QuantumCode
theorem _root_.solution (C : QuantumCode H) :
    LinearMap.IsSymmetric C.projector := by
  simpa [projector] using C.carrier.starProjection_isSymmetric
end QEC.Semantics.QuantumCode
