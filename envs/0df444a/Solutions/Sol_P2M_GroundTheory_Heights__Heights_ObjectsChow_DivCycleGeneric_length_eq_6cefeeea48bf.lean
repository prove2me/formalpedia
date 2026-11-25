-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_length_eq_6cefeeea48bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:08.138173+00:00
-- url     : https://prove2.me/submissions/3c8b1bd3-74a6-4790-9f96-1da774394b9b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
open MvPolynomial
variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] (S : Submonoid A)
  [IsLocalization S A']
namespace GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
theorem _root_.solution (J W : Ideal A) [W.IsPrime] (hW : Disjoint (S : Set A) W)
    [(W.map (algebraMap A A')).IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) =
      Module.length (Localization.AtPrime (W.map (algebraMap A A')))
        (Localization.AtPrime (W.map (algebraMap A A')) ⧸
          (J.map (algebraMap A A')).map (algebraMap A' (Localization.AtPrime (W.map (algebraMap A A'))))) := by
  set W' := W.map (algebraMap A A')
  set L := Localization.AtPrime W'
  have hc : W'.comap (algebraMap A A') = W :=
    IsLocalization.under_map_of_isPrime_disjoint S A' ‹_› hW
  have hL : IsLocalization.AtPrime L W := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S L W'
    convert this using 2 ; exact hc.symm
  let e : Localization.AtPrime W ≃ₐ[A] L := IsLocalization.algEquiv W.primeCompl _ _
  let _ : Algebra (Localization.AtPrime W) L := e.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower A (Localization.AtPrime W) L :=
    IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  let g := (J : Submodule A A).toLocalizedQuotient' L W.primeCompl (Algebra.linearMap A L)
  have h1 := ((IsLocalizedModule.iso W.primeCompl g).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq
  have h2 := Module.length_eq_of_surjective (S := Localization.AtPrime W) (R := L)
    (M := L ⧸ (J : Submodule A A).localized' L W.primeCompl (Algebra.linearMap A L)) e.surjective
  have h3 : (J : Submodule A A).localized' L W.primeCompl (Algebra.linearMap A L) =
      (J.map (algebraMap A A')).map (algebraMap A' L) := by
    rw [Submodule.localized'_eq_span, Ideal.map_map, ← IsScalarTower.algebraMap_eq, Ideal.map]
    rfl
  rw [h1, h2, h3]
end GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
