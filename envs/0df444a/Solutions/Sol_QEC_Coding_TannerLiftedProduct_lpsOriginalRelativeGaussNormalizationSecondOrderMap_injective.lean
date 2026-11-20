-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationSecondOrderMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:36:48.067114+00:00
-- url     : https://prove2.me/submissions/4969b718-cb56-464c-a186-f70c89ec25fb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondOrderMap_generatedDiagram

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    Function.Injective (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalGaussAffineOrder_domain N hN p
  let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  let := lpsOriginalGaussAffineGenerated_isFractionRing N hN p
  have hg : Function.Injective (lpsOriginalGaussAffineToGenerated N hN p) :=
    IsFractionRing.injective (LPSOriginalGaussAffineOrder N hN p)
      (lpsOriginalGeneratedFunctionFieldQ N hN)
  intro a b hab
  apply hg
  apply (lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)).injective
  rw [← lpsOriginalRelativeGaussNormalizationSecondOrderMap_generatedDiagram
      N p hNp h4N hN hpN a,
    ← lpsOriginalRelativeGaussNormalizationSecondOrderMap_generatedDiagram
      N p hNp h4N hN hpN b,hab]
end QEC.Coding.TannerLiftedProduct
