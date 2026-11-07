-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_nested_annihilator_germ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:42:43.513144+00:00
-- url     : https://prove2.me/submissions/ac97a5a5-c65e-4efd-aed2-d958f356c124

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicJFunctionCoefficient_eval__80431591df58
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFullMeromorphicJFractionEmbedding_polynomial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (Φ : Polynomial (Polynomial ℂ))
    (hΦ : ∀ τ : ℍ, Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (F (Sum.inl ⟦τ⟧)) = 0) :
    Φ.eval₂ ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))))
      (lpsOriginalFilledMeromorphicRestriction N hN F hF) = 0 := by
  let e := (lpsOriginalMeromorphicGermSubring UpperHalfPlane.upperHalfPlaneSet).subtype.comp
    (lpsOriginalFilledMeromorphicRestrictionSubfield N hN).subtype
  let g : (ℂ → ℂ) →+* Filter.Germ (Filter.codiscreteWithin
      UpperHalfPlane.upperHalfPlaneSet) ℂ :=
    Filter.Germ.coeRingHom (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet)
  have hc : e.comp ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))) =
      g.comp lpsOriginalMeromorphicJFunctionCoefficient := by
    apply RingHom.ext
    intro P
    exact lpsOriginalFullMeromorphicJFractionEmbedding_polynomial N hN P
  have hfun : Φ.eval₂ lpsOriginalMeromorphicJFunctionCoefficient
      (lpsOriginalFilledMeromorphicPullback N F) = 0 := by
    funext z
    rw [lpsOriginalMeromorphicJFunctionCoefficient_eval₂]
    exact hΦ (UpperHalfPlane.ofComplex z)
  have he := Polynomial.hom_eval₂ Φ
    ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))) e
    (lpsOriginalFilledMeromorphicRestriction N hN F hF)
  rw [hc] at he
  have hx : e (lpsOriginalFilledMeromorphicRestriction N hN F hF) =
      g (lpsOriginalFilledMeromorphicPullback N F) := rfl
  rw [hx,←Polynomial.hom_eval₂,hfun,map_zero] at he
  apply Subtype.ext
  apply Subtype.ext
  exact he
end QEC.Coding.TannerLiftedProduct
