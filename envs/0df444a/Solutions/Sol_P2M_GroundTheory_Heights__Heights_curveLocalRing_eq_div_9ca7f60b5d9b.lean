-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_curveLocalRing_eq_div_9ca7f60b5d9b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:14.62109+00:00
-- url     : https://prove2.me/submissions/0801fe7f-3f37-494d-b7fd-617a2fa54f31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_curveLocalRing_358a5a627391


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
open MvPolynomial ComplexSets FieldNumbers
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (o : curveLocalRing I q) : ∃ f s, IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) s) ∧
      o * algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) s =
        algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f := by
  obtain ⟨z, rfl⟩ : ∃ z, Ideal.Quotient.mk
      (I.map (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))))) z = o :=
    Ideal.Quotient.mk_surjective o
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker (eval q)).primeCompl z
  refine ⟨f, s, isUnit_algebraMap_curveLocalRing I q s fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have e := congrArg (Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))))))
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker (eval q))) f s)
  rw [map_mul] at e
  exact e
end GroundTheory.Heights₂.Heights
