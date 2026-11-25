-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_nonempty_normalModel_of_presentation_27235b04eeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:37:00.315905+00:00
-- url     : https://prove2.me/submissions/f3f83b4a-1ada-4229-8352-ee1376b449e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelExists
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NonemptyNormalModelOfPresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelExists
import Theorems.Thm_UpperTheory_Reformulated_B_Gc5_nonempty_normalModel_of_presentation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] FractionRing.liftAlgebra
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (R : Type)
    [CommRing R] [IsDomain R] [Algebra ℂ R] (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = J) : Nonempty (NormalModel J) :=
  _root_.UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_presentation J R π hπ hker
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
