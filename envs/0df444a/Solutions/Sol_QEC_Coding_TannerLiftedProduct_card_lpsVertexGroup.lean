-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsVertexGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:40:47.033945+00:00
-- url     : https://prove2.me/submissions/2a787b65-b200-4153-8ddb-f173561316cc

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_card_psl


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    Fintype.card (LPSVertexGroup hp hp4 n) =
      let q := (lpsResiduePrimeSequence hp hp4 n).q
      q * (q ^ 2 - 1) / 2 :=
  (lpsResiduePrimeSequence hp hp4 n).card_psl
end QEC.Coding.TannerLiftedProduct
