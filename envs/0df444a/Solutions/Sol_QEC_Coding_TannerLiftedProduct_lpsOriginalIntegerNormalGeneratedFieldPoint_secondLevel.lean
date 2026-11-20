-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGeneratedFieldPoint_secondLevel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:58:22.234533+00:00
-- url     : https://prove2.me/submissions/41498d3d-87ea-4ebe-93fc-fdb0795bac53

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGeneratedFieldPoint_level
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
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerNormalGeneratedFieldPoint M hM ≫
      lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM =
    Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM)) ≫
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let fN := lpsOriginalIntegerNormalGluedFricke N hN
  let fM := lpsOriginalIntegerNormalGluedFricke M hM
  let L := lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM
  let u := lpsOriginalIntegerNormalGeneratedFieldPoint M hM
  let v := lpsOriginalIntegerNormalGeneratedFieldPoint N hN
  let pN := Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickePullback N hN))
  let pM := Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickePullback M hM))
  let li := Spec.map (CommRingCat.ofHom (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom)
  have hm : u ≫ fM = pM ≫ u := lpsOriginalIntegerNormalGeneratedFieldPoint_fricke M hM
  have hl : u ≫ L = li ≫ v :=
    (lpsOriginalIntegerNormalGeneratedFieldPoint_level N M hNM h4N hN hM).symm
  have hn : v ≫ fN = pN ≫ v := lpsOriginalIntegerNormalGeneratedFieldPoint_fricke N hN
  have he : pM ≫ li ≫ pN =
      Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  change u ≫ (fM ≫ L ≫ fN) = _
  calc
    u ≫ (fM ≫ L ≫ fN) = (u ≫ fM) ≫ (L ≫ fN) := (Category.assoc _ _ _).symm
    _ = (pM ≫ u) ≫ (L ≫ fN) := congrArg (fun f => f ≫ (L ≫ fN)) hm
    _ = pM ≫ ((u ≫ L) ≫ fN) := by simp only [Category.assoc]
    _ = pM ≫ ((li ≫ v) ≫ fN) := congrArg (fun f => pM ≫ (f ≫ fN)) hl
    _ = pM ≫ (li ≫ (v ≫ fN)) := by rw [Category.assoc]
    _ = pM ≫ (li ≫ (pN ≫ v)) := congrArg (fun f => pM ≫ (li ≫ f)) hn
    _ = (pM ≫ li ≫ pN) ≫ v := by simp only [Category.assoc]
    _ = _ := congrArg (fun f => f ≫ v) he
end QEC.Coding.TannerLiftedProduct
