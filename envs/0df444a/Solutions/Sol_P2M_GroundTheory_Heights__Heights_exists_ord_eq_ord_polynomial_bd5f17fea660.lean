-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_ord_eq_ord_polynomial_bd5f17fea660
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:31:17.17127+00:00
-- url     : https://prove2.me/submissions/b83cfb38-0ea7-445c-a750-c4f7e176e943

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOrdDeterminesPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_POrdDeterminesPlace
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
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (a : curveLocalRing I q) : ∃ f : MvPolynomial (Fin n) ℂ, ∀ P : MaximalSpectrum (curveNormalisation I q),
      Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
        Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨⟨f, h⟩, hfh⟩ := IsLocalization.mk'_surjective (RingHom.ker (eval q)).primeCompl y
  refine ⟨f, fun P ↦ ?_⟩
  have hu : IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (h : MvPolynomial (Fin n) ℂ)) :=
    isUnit_algebraMap_curveLocalRing I q h fun H ↦ h.2 (RingHom.mem_ker.2 H)
  let π : Localization.AtPrime (RingHom.ker (eval q)) →+* curveLocalRing I q := Ideal.Quotient.mk _
  have hπ : ∀ g : MvPolynomial (Fin n) ℂ, algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) g =
      π (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) g) := fun _ ↦ rfl
  have hy' : π y = a := hy
  have hfh' : IsLocalization.mk' (Localization.AtPrime (RingHom.ker (eval q))) f h = y := hfh
  have heq : a *
      algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (h : MvPolynomial (Fin n) ℂ) =
      algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f := by
    rw [← hy', ← hfh', hπ, hπ, ← map_mul, IsLocalization.mk'_spec]
  rw [← heq, map_mul, map_mul, Ring.ord_mul_of_isUnit_right ((hu.map _).map _)]
end GroundTheory.Heights₂.Heights
