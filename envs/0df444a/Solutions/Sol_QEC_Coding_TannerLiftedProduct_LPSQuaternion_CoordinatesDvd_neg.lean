-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSQuaternion.CoordinatesDvd.neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:59:21.303626+00:00
-- url     : https://prove2.me/submissions/f37e372b-fa8b-42ad-b746-f68cee0c9e86

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
namespace LPSQuaternion.CoordinatesDvd
theorem _root_.solution
    {s : ℤ} {t : LPSQuaternion} (ht : t.CoordinatesDvd s) :
    (-t).CoordinatesDvd s := by
  rcases ht with ⟨ha, hb, hc, hd⟩
  exact ⟨dvd_neg.mpr ha, dvd_neg.mpr hb,
    dvd_neg.mpr hc, dvd_neg.mpr hd⟩
end LPSQuaternion.CoordinatesDvd
end QEC.Coding.TannerLiftedProduct
