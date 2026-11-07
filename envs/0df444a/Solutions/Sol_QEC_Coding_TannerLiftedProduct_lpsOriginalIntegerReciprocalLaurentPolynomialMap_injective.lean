-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalLaurentPolynomialMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:36:45.004072+00:00
-- url     : https://prove2.me/submissions/7af784d7-a2a4-49d5-bd07-b7054ea5ddf8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Function.Injective lpsOriginalIntegerReciprocalLaurentPolynomialMap :=
  (LaurentPolynomial.invert (R := ℤ)).injective.comp Polynomial.toLaurent_injective
end QEC.Coding.TannerLiftedProduct
