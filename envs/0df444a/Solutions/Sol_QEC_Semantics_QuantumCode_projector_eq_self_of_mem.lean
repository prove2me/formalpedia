-- Prove2me | solution 1 for QEC.Semantics.QuantumCode.projector_eq_self_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:06:23.546845+00:00
-- url     : https://prove2.me/submissions/4a499ea4-22ff-4001-9db8-86805e4a8188

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_iff_mem

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
theorem _root_.solution (C : QuantumCode H) {v : H} (hv : v ∈ C.carrier) :
    C.projector v = v :=
  (C.projector_eq_self_iff_mem).2 hv
end QEC.Semantics.QuantumCode
