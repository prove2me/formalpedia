-- Prove2me | solution 1 for QEC.Semantics.QuantumCode.projector_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:10:59.940531+00:00
-- url     : https://prove2.me/submissions/e8a77f1f-d435-46a0-a5b8-d29bbe36867f

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_mem_carrier
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_of_mem

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
    C.projector.comp C.projector = C.projector := by
  ext v
  exact C.projector_eq_self_of_mem (C.projector_mem_carrier v)
end QEC.Semantics.QuantumCode
