-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ConeLocalLength_proof_35f32fadaed3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:01:49.796806+00:00
-- url     : https://prove2.me/submissions/e381ee85-e04a-4a43-9cf9-dd73696af7eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeLocalLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeLocalFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsLocalizedQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PConeLocalLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_algebraMap_cone_coe_8ba24d60fc2f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing
noncomputable section
universe u
set_option maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace ConeLocalLength
theorem _root_.solution (h₁ : LocalizedQuotientLength.Statement.{u, u})
    (h₂ : ConeLocalFlat.Statement.{u}) : ConeLocalLength.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW c a h _ _ hhW α hα
  have := hP.isPrime
  have := hW.isPrime
  obtain ⟨_, _, _, hmax⟩ := h₂ F K ι P hP W hW hPW
  have : IsLocalHom (algebraMap (degZeroLoc P {W}) (coneLocal P W hPW)) :=
    ((local_hom_TFAE _).out 2 0).mp hmax.le
  have hu : IsUnit (algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P h)) :=
    IsLocalization.map_units (coneLocal P W hPW)
      (⟨_, ⟨h, hhW, rfl⟩⟩ : W.primeCompl.map (Ideal.Quotient.mk P))
  have hne : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P h) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h' => hhW (hPW h')
  have ha : algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P a) =
      algebraMap (degZeroLoc P {W}) (coneLocal P W hPW) α *
        algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P h) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, degZeroLoc.algebraMap_cone_coe, Subalgebra.coe_algebraMap,
      Subalgebra.coe_algebraMap, hα, div_mul_cancel₀ _ hne]
  have hspan : Ideal.span {algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P a)} =
      (Ideal.span {α}).map (algebraMap (degZeroLoc P {W}) (coneLocal P W hPW)) := by
    rw [Ideal.map_span, Set.image_singleton, ha, Ideal.span_singleton_mul_right_unit hu]

  have key : ∀ (A R : Type u) [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R]
      [Algebra A R] [IsLocalHom (algebraMap A R)] [Module.Flat A R],
      (maximalIdeal A).map (algebraMap A R) = maximalIdeal R → ∀ x : A,
        Module.length R (R ⧸ (Ideal.span {x}).map (algebraMap A R)) = Ring.ord A x := by
    intro A R _ _ _ _ _ _ _ hm x
    have hs : Module.length R (R ⧸ maximalIdeal R) = 1 := Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩)
    rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (Ideal.span {x})).toLinearEquiv.length_eq,
      IsLocalRing.length_baseChange, hm, hs, mul_one]
    rfl
  unfold multAt
  rw [h₁ _ P W a (coneLocal P W hPW) inferInstance, hspan]
  exact key (degZeroLoc P {W}) (coneLocal P W hPW) hmax α
end ConeLocalLength
end GroundTheory.Heights₂.Heights.FieldNumbers
