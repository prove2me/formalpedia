-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyLabel_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:46:40.20246+00:00
-- url     : https://prove2.me/submissions/14b187e9-5161-46c5-8c59-2e41b140eab7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionPSL_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    lpsEffectiveQuaternionFamilyLabel hp hp4 n =
      lpsQuaternionLabel (lpsEffectiveResiduePrimeAt hp hp4 n) := by
  funext t
  exact lpsEffectiveQuaternionPSL_eq _ t.1 _
end QEC.Coding.TannerLiftedProduct
