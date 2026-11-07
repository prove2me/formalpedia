-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJAffinePoint_crossChart_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:55:34.374647+00:00
-- url     : https://prove2.me/submissions/f23b3d91-c177-4c58-87b6-a144784a7e47

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJCharts_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R : Type) [CommRing R] (x y : R)
    (h : lpsOriginalIntegerProjectiveJAffinePoint R false x =
      lpsOriginalIntegerProjectiveJAffinePoint R true y) : x*y=1 := by
  let fx : Spec (.of R) ⟶ Spec (.of (Polynomial ℤ)) :=
    Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom R) x))
  let fy : Spec (.of R) ⟶ Spec (.of (Polynomial ℤ)) :=
    Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom R) y))
  have hc : fx ≫ lpsOriginalIntegerProjectiveJChartMap false =
      fy ≫ lpsOriginalIntegerProjectiveJChartMap true := h
  let l := lpsOriginalIntegerProjectiveJCharts_pullback.lift fx fy hc
  let φ : LaurentPolynomial ℤ →+* R := (Spec.preimage l).hom
  have hl0 := lpsOriginalIntegerProjectiveJCharts_pullback.lift_fst fx fy hc
  change l ≫ Spec.map (CommRingCat.ofHom
    (Polynomial.toLaurent : Polynomial ℤ →+* LaurentPolynomial ℤ)) = fx at hl0
  rw [← Spec.map_preimage l,← Spec.map_comp] at hl0
  have he0 := congrArg (fun f : CommRingCat.of (Polynomial ℤ) ⟶ CommRingCat.of R =>
    f.hom Polynomial.X) (Spec.map_injective hl0)
  have hx : φ (LaurentPolynomial.T (1 : ℤ))=x := by
    simpa [φ,fx,CommRingCat.hom_comp,RingHom.comp_apply,
      Polynomial.toLaurent_X,Polynomial.eval₂RingHom] using he0
  have hl1 := lpsOriginalIntegerProjectiveJCharts_pullback.lift_snd fx fy hc
  change l ≫ Spec.map (CommRingCat.ofHom
    lpsOriginalIntegerReciprocalLaurentPolynomialMap) = fy at hl1
  rw [← Spec.map_preimage l,← Spec.map_comp] at hl1
  have he1 := congrArg (fun f : CommRingCat.of (Polynomial ℤ) ⟶ CommRingCat.of R =>
    f.hom Polynomial.X) (Spec.map_injective hl1)
  have hy : φ (LaurentPolynomial.T (-1 : ℤ))=y := by
    simpa [φ,fy,CommRingCat.hom_comp,RingHom.comp_apply,
      lpsOriginalIntegerReciprocalLaurentPolynomialMap,Polynomial.toLaurent_X,
      LaurentPolynomial.invert_T,Polynomial.eval₂RingHom] using he1
  calc
    x*y = φ (LaurentPolynomial.T (1 : ℤ))*φ (LaurentPolynomial.T (-1 : ℤ)) := by rw [hx,hy]
    _ = φ (LaurentPolynomial.T (1 : ℤ)*LaurentPolynomial.T (-1 : ℤ)) := (map_mul φ _ _).symm
    _ = φ (LaurentPolynomial.T (0 : ℤ)) := by congr 1; rw [← LaurentPolynomial.T_add]; rfl
    _ = 1 := by rw [LaurentPolynomial.T_zero,map_one]
end QEC.Coding.TannerLiftedProduct
