-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Loc.Ptf.trace_comp_smulRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:53.726657+00:00
-- url     : https://prove2.me/submissions/dec5848e-3eb2-473c-b0de-1da109ac30ff

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_LocalTraceForms_TraceCompSmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Loc PositivityTheory.RgUd.TP.Loc.Ptf
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
namespace PositivityTheory.RgUd.TP.Loc.Ptf
theorem _root_.solution {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : W →ₗ[K] W) (φ : Module.Dual K W) (w : W) : LinearMap.trace K W (f * φ.smulRight w) = φ (f w) := by
  have e : f * φ.smulRight w = φ.smulRight (f w) := by
    ext u
    simp
  have e2 : φ.smulRight (f w) = dualTensorHom K W W (φ ⊗ₜ f w) := by
    ext u
    simp [dualTensorHom_apply]
  rw [e, e2, LinearMap.trace_eq_contract_apply]
  simp
end PositivityTheory.RgUd.TP.Loc.Ptf
