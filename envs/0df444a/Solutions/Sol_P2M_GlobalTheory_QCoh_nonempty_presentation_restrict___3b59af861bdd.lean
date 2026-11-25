-- Prove2me | solution 1 for P2M_GlobalTheory_QCoh_nonempty_presentation_restrict___3b59af861bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:31:48.154558+00:00
-- url     : https://prove2.me/submissions/53f438fd-da0d-4cd0-a99d-03379b13530f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_nonempty_presentation_Spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.QCoh
theorem _root_.solution (hU : IsAffineOpen U)
    [(F.restrict hU.fromSpec).IsQuasicoherent] : Nonempty (F.restrict U.ι).Presentation := by
  obtain ⟨P⟩ := nonempty_presentation_Spec (F.restrict hU.fromSpec)
  let iso : Scheme.Modules.restrictFunctor hU.fromSpec ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom ≅ Scheme.Modules.restrictFunctor U.ι :=
    (Scheme.Modules.restrictFunctorComp _ _).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec
  exact ⟨SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso.app F).hom
    (Scheme.Modules.presentationRestrict hU.isoSpec.hom P)⟩
end GlobalTheory.QCoh
