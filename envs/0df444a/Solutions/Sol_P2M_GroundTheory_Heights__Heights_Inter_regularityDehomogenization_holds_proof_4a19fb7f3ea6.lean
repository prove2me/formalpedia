-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityDehomogenization_holds_proof_4a19fb7f3ea6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:52.994857+00:00
-- url     : https://prove2.me/submissions/b5b6988a-95e3-400d-aeef-7d099348dbf7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PrimeComplMapLeNonZeroDivisorsQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsLocalizedQuotientLength
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsLast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_locIdeal_eq_span_6d401f7ea2c7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_locRing_algebraMap_cone_coe_cb5a4a87300e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomogIdeal_of_mem_minimalPrimes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace regularityDehomogenization_holds
theorem _root_.solution (h₁ : GroundTheory.Heights₂.Heights.FieldNumbers.LocalizedQuotientLength.Statement.{0, 0})
    (h₂ : regularityLocalFlat_holds.Statement) : regularityDehomogenization_holds.Statement := by
  intro K _ ι _ P s t a W y hP hs hsP hW ht htW hy
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  have := hP.1
  have := hWp
  have hWm : IsMultiProjPrime W := ⟨hWp, isMultiHomogIdeal_of_mem_minimalPrimes hP.2.1 hs hW.1, hW.2⟩

  have htnz : Ideal.Quotient.mk P t ∈ nonZeroDivisors (MRing ι ⧸ P) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => htW (hPW h)
  have hyO : y ∈ locRing P W := by
    refine Subring.subset_closure ⟨s, t, a, htnz, htW, hs, ht, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    exact hy
  refine ⟨hyO, ?_⟩
  obtain ⟨_, _, _, hmax⟩ := h₂ K ι P W hP hWm hPW
  have : IsLocalHom (algebraMap (locRing P W) (coneLocRing P W hPW)) :=
    ((local_hom_TFAE _).out 2 0).mp hmax.le

  have hu : IsUnit (algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P t)) :=
    IsLocalization.map_units (coneLocRing P W hPW)
      (⟨_, ⟨t, htW, rfl⟩⟩ : W.primeCompl.map (Ideal.Quotient.mk P))
  have hs' : algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P s) =
      algebraMap (locRing P W) (coneLocRing P W hPW) ⟨y, hyO⟩ *
        algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P t) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, locRing.algebraMap_cone_coe, Subalgebra.coe_algebraMap,
      Subalgebra.coe_algebraMap, hy]
  have hspan : Ideal.span {algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P s)} =
      (Ideal.span {(⟨y, hyO⟩ : locRing P W)}).map (algebraMap (locRing P W) (coneLocRing P W hPW)) := by
    rw [Ideal.map_span, Set.image_singleton, hs', Ideal.span_singleton_mul_right_unit hu]

  have key : ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
      [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B],
      (maximalIdeal A).map (algebraMap A B) = maximalIdeal B → ∀ x : A,
        Module.length B (B ⧸ (Ideal.span {x}).map (algebraMap A B)) = Module.length A (A ⧸ Ideal.span {x}) := by
    intro A B _ _ _ _ _ _ _ hm x
    have hres : Module.length B (B ⧸ maximalIdeal B) = 1 := Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩)
    rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (Ideal.span {x})).toLinearEquiv.length_eq,
      IsLocalRing.length_baseChange, hm, hres, mul_one]
  unfold multAt
  rw [dif_pos hWp, h₁ (MRing ι) P W s (coneLocRing P W hPW) inferInstance, hspan, locIdeal_eq_span hyO,
    key (locRing P W) (coneLocRing P W hPW) hmax]
end regularityDehomogenization_holds
end GroundTheory.Heights₂.Heights.Inter
