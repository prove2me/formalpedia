-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:45:56.02444+00:00
-- url     : https://prove2.me/submissions/c42b667c-f526-4583-98aa-5cea56c01197

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    lpsQuaternionWordProduct ([] : List (LPSGeneratorIndex p)) = 1 := rfl
end QEC.Coding.TannerLiftedProduct
