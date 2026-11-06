-- Prove2me | solution 1 for QEC.Semantics.QuantumCode.projector_adjoint_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:39:11.877344+00:00
-- url     : https://prove2.me/submissions/621460ce-85a7-4100-bfba-181da497547d

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_isSymmetric

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
    LinearMap.adjoint C.projector = C.projector :=
  (C.projector_isSymmetric).adjoint_eq
end QEC.Semantics.QuantumCode
