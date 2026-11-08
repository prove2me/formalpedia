-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyIndex_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:46:44.93384+00:00
-- url     : https://prove2.me/submissions/6555b8e0-be47-4593-bc76-8e60a9d83bb0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) (t : LPSGeneratorIndex p) :
    (lpsPSLEnumerationEquiv (lpsEffectiveResiduePrimeAt hp hp4 n).q)
      (lpsEffectiveQuaternionFamilyIndex hp hp4 n t) =
        lpsEffectiveQuaternionFamilyLabel hp hp4 n t := by
  exact (lpsPSLEnumerationEquiv _).apply_symm_apply _
end QEC.Coding.TannerLiftedProduct
