-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationEquiv_base_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:28:52.018455+00:00
-- url     : https://prove2.me/submissions/d8bf04c0-7459-4a60-a80a-1e902c89fbce

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeToGenerated_base_coe

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (c : LPSOriginalGaussAffineOrder N hN p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
      ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
    ((lpsOriginalRelativeGaussNormalizationEquiv N p hNp h4N hN hpN
      (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p) c)).val.val) =
      (lpsOriginalGaussAffineToGenerated N hN p c).val := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let A := LPSOriginalGaussBase p
  let B := LPSOriginalRelativeGaussHeckeOrder N hN p
  let L := lpsOriginalGeneratedFunctionFieldQ (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  let := (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).toAlgebra
  let : Algebra A L := ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
    (algebraMap A B)).toAlgebra
  let : IsScalarTower A B L := .of_algebraMap_eq' rfl
  let := lpsOriginalRelativeGaussHeckeOrder_isIntegralClosure N p hNp h4N hN hpN
  have he := IsIntegralClosure.algebraMap_equiv A B L (integralClosure A L)
    (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p) c)
  change (lpsOriginalRelativeGaussNormalizationEquiv N p hNp h4N hN hpN
    (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p) c)).val = _ at he
  exact (congrArg Subtype.val he).trans
    (lpsOriginalRelativeGaussHeckeToGenerated_base_coe N p hNp h4N hN c)
end QEC.Coding.TannerLiftedProduct
