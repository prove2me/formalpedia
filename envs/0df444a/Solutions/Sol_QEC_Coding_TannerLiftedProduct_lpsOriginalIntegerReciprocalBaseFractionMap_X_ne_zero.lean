-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalBaseFractionMap_X_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:36:53.300502+00:00
-- url     : https://prove2.me/submissions/8f9a957e-cabb-4df7-a7b1-c1e8c8f484ee

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalBaseFractionMap_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    lpsOriginalIntegerReciprocalBaseFractionMap Polynomial.X≠0 :=
  (map_ne_zero_iff _ lpsOriginalIntegerReciprocalBaseFractionMap_injective).mpr
    Polynomial.X_ne_zero
end QEC.Coding.TannerLiftedProduct
