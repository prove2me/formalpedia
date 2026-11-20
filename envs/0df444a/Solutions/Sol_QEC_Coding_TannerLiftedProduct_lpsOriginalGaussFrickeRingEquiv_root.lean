-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussFrickeRingEquiv_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:16:41.01158+00:00
-- url     : https://prove2.me/submissions/baadfbb3-c705-4355-a13c-c0a124c40e9f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalGaussFrickeRingEquiv N hN p hpN (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)) = AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X) :=
  lpsOriginalGaussFrickeOrderMap_root N hN p hpN
end QEC.Coding.TannerLiftedProduct
