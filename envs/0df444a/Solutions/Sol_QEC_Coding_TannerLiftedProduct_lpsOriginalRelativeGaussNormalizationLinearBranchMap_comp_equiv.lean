-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationLinearBranchMap_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:59:05.875615+00:00
-- url     : https://prove2.me/submissions/b7c0f4ce-daad-450b-b87a-1c4bae03dc13

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiberEquiv_mk


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q).comp
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN).toRingHom =
      lpsOriginalRelativeGaussHeckeLinearBranchMap N hN p hpN q := by
  apply RingHom.ext
  intro x
  change (lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _
        (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN x))).1 =
    (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q (Ideal.Quotient.mk _ x)).1
  rw [lpsOriginalRelativeGaussNormalizationFiberEquiv_mk]
end QEC.Coding.TannerLiftedProduct
