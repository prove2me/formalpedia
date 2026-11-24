-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_pointLocalRing_0914499906a4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:45.972516+00:00
-- url     : https://prove2.me/submissions/1c42c747-b5b4-440b-95ff-9bff9c4d265b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {σ : Type*}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (f : MvPolynomial σ ℂ)
    (hf : eval w f ≠ 0) : IsUnit (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) f) := by
  have hu : IsUnit (algebraMap (MvPolynomial σ ℂ)
      (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))) f) :=
    IsLocalization.map_units _
      (⟨f, fun h ↦ hf (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).primeCompl)
  exact hu.map (Ideal.Quotient.mk _)
end GroundTheory.Heights₂.Heights
