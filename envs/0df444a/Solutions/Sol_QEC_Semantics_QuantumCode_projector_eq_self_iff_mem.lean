-- Prove2me | solution 1 for QEC.Semantics.QuantumCode.projector_eq_self_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:02:03.927533+00:00
-- url     : https://prove2.me/submissions/462da551-d0c8-49ef-b9ce-f74517a7b9d9

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
theorem _root_.solution (C : QuantumCode H) {v : H} :
    C.projector v = v ↔ v ∈ C.carrier := by
  simpa [projector] using (Submodule.starProjection_eq_self_iff (K := C.carrier) (v := v))
end QEC.Semantics.QuantumCode
