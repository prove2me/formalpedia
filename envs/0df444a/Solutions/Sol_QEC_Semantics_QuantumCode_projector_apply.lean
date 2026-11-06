-- Prove2me | solution 1 for QEC.Semantics.QuantumCode.projector_apply
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:37:10.671773+00:00
-- url     : https://prove2.me/submissions/ad6f41a9-2448-4dab-b72d-8dab41c58e62

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

theorem solution (C : QuantumCode H) (v : H) :
    C.projector v = C.carrier.starProjection v := by
  solve | rfl | simp | omega | norm_num | simp_all
