-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyIndex_decode_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:16:42.608315+00:00
-- url     : https://prove2.me/submissions/b91ed770-1b0f-4172-90b8-5b28cd8d9450

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionFamilyIndex_decode
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionFamilyLabel_eq_original

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) (t : LPSGeneratorIndex p) :
    (lpsPSLEnumerationEquiv (lpsResiduePrimeSequence hp hp4 n).q)
        (lpsEffectiveQuaternionFamilyIndex hp hp4 n t) =
      lpsQuaternionFamilyLabel hp hp4 n t := by
  exact (lpsEffectiveQuaternionFamilyIndex_decode hp hp4 n t).trans
    (congrFun (lpsEffectiveQuaternionFamilyLabel_eq_original hp hp4 n) t)
end QEC.Coding.TannerLiftedProduct
