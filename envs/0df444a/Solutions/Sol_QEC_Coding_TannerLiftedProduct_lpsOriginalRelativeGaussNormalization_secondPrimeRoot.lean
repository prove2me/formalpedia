-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondPrimeRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:40:55.807395+00:00
-- url     : https://prove2.me/submissions/cdcf6f98-026f-44a8-b1b4-017ba244f8ac

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondJ_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFirstJ_coe

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN))
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let : Algebra (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
    ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
  let f : LPSOriginalRelativeGaussNormalization N p hNp h4N hN →+*
      LPSOriginalHolomorphicFractionField :=
    (lpsOriginalGeneratedFunctionFieldQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).val.toRingHom.comp
      (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos))).val.toRingHom
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  apply hf
  rw [Polynomial.hom_eval₂,map_zero,lpsOriginalBivariateIntegerCoefficientEval_comp_hom]
  change (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom LPSOriginalHolomorphicFractionField)
      (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN).val.val)
    (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN).val.val = 0
  rw [lpsOriginalRelativeGaussNormalizationFirstJ_coe,
    lpsOriginalRelativeGaussNormalizationSecondJ_coe]
  exact lpsOriginalIntegerPolynomial_ambientRoot p (Fact.out : p.Prime).pos
end QEC.Coding.TannerLiftedProduct
