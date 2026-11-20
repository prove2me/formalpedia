-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussFrickeRingEquiv_j
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:16:44.204455+00:00
-- url     : https://prove2.me/submissions/705223fc-4025-4a26-9e71-5b2659de5762

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalGaussFrickeRingEquiv N hN p hpN (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)) = AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p) :=
  lpsOriginalGaussFrickeOrderMap_j N hN p hpN
end QEC.Coding.TannerLiftedProduct
