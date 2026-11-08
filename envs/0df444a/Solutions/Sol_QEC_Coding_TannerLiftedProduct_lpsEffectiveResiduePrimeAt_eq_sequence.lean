-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveResiduePrimeAt_eq_sequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:51:25.580413+00:00
-- url     : https://prove2.me/submissions/1699a96d-bfb7-49ec-8090-b949265d0048

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    lpsEffectiveResiduePrimeAt hp hp4 n = lpsResiduePrimeSequence hp hp4 n := rfl
end QEC.Coding.TannerLiftedProduct
