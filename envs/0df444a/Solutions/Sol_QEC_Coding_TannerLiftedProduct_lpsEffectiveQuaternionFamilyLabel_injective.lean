-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyLabel_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:16:21.562986+00:00
-- url     : https://prove2.me/submissions/b06c955e-702a-4ea5-84a0-eab121b5f31f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionFamilyLabel_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionLabel_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    Function.Injective (lpsEffectiveQuaternionFamilyLabel hp hp4 n) := by
  rw [lpsEffectiveQuaternionFamilyLabel_eq]
  exact lpsQuaternionLabel_injective (lpsEffectiveResiduePrimeAt hp hp4 n)
end QEC.Coding.TannerLiftedProduct
