-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:44:53.159173+00:00
-- url     : https://prove2.me/submissions/e2116c60-6187-406b-bfc5-19d82c4457da

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_first
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Injective (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let e := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
  intro x y h
  have hx := congrArg (fun f : K →+* K × K => f x)
    (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_first
      N p hNp h4N hN hpN q)
  have hy := congrArg (fun f : K →+* K × K => f y)
    (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_first
      N p hNp h4N hN hpN q)
  change e (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q x) = (x, x^p) at hx
  change e (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q y) = (y, y^p) at hy
  have hxy := congrArg e h
  exact congrArg Prod.fst (hx.symm.trans (hxy.trans hy))
end QEC.Coding.TannerLiftedProduct
