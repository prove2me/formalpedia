-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveResiduePrimeAt_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:46:37.26764+00:00
-- url     : https://prove2.me/submissions/f646827b-6244-4563-9af9-69f9dd390a93

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    (lpsEffectiveResiduePrimeAt hp hp4 B).q = lpsLeastPrimeAbove hp B := rfl
end QEC.Coding.TannerLiftedProduct
