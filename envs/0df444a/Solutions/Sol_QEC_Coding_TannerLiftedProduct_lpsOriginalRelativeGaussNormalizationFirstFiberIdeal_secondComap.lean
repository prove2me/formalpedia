-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFirstFiberIdeal_secondComap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:36:57.358645+00:00
-- url     : https://prove2.me/submissions/a428e8a0-31ba-443f-b71c-e0509ea0b64c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)).comap
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN) = q := by
  ext c
  exact lpsOriginalRelativeGaussNormalizationSecondOrder_mem_firstFiberIdeal_iff
    N p hNp h4N hN hpN q c
end QEC.Coding.TannerLiftedProduct
