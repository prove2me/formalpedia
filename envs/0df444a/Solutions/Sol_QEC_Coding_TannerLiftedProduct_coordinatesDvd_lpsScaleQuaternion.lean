-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coordinatesDvd_lpsScaleQuaternion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:59:35.797722+00:00
-- url     : https://prove2.me/submissions/e5a3a0eb-28db-4f22-b009-67fb86f7eb4d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (s : ℤ) (t : LPSQuaternion) :
    (lpsScaleQuaternion s t).CoordinatesDvd s := by
  exact ⟨⟨t.a, rfl⟩, ⟨t.b, rfl⟩, ⟨t.c, rfl⟩, ⟨t.d, rfl⟩⟩
end QEC.Coding.TannerLiftedProduct
