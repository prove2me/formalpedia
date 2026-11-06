-- Prove2me | solution 2 for QEC.Semantics.QuantumCode.projector_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:43:12.293459+00:00
-- url     : https://prove2.me/submissions/7713ba40-6284-4897-bc7b-cf38a9d00f43

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport

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
theorem _root_.solution (C : QuantumCode H) (v : H) :
    C.projector v = C.carrier.starProjection v :=
  rfl
end QEC.Semantics.QuantumCode
