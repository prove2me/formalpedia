-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussNormalization_etale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:33:57.426668+00:00
-- url     : https://prove2.me/submissions/ad9e57c2-0252-4338-9592-d91e1b7f0d7b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineOrder_etale

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
    let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
      ((lpsOriginalGaussAffineToGenerated N hN p).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
    Algebra.Etale (LPSOriginalGaussBase p)
      (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ((lpsOriginalGaussAffineToGenerated N hN p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
  let := lpsOriginalGaussAffineOrder_etale N hN p hpN
  exact Algebra.Etale.of_equiv (lpsOriginalGaussNormalizationEquiv N hN p hpN)
end QEC.Coding.TannerLiftedProduct
