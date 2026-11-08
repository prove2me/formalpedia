-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyLabel_eq_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:09:58.061207+00:00
-- url     : https://prove2.me/submissions/99b8f3c6-80b9-4e24-840a-82252a66e182

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionFamilyLabel_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    lpsEffectiveQuaternionFamilyLabel hp hp4 n = lpsQuaternionFamilyLabel hp hp4 n :=
  lpsEffectiveQuaternionFamilyLabel_eq hp hp4 n
end QEC.Coding.TannerLiftedProduct
