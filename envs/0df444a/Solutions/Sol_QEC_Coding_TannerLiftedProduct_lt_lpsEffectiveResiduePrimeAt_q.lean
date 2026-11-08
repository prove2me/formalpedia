-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lt_lpsEffectiveResiduePrimeAt_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:09:26.868188+00:00
-- url     : https://prove2.me/submissions/7b58a3a2-c6ec-4c3a-b255-a01ce06cd1b2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lt_lpsResiduePrimeAt


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    B < (lpsEffectiveResiduePrimeAt hp hp4 B).q :=
  lt_lpsResiduePrimeAt hp hp4 B
end QEC.Coding.TannerLiftedProduct
