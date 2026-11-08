-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsResidueY_eq_minusRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:55:21.397214+00:00
-- url     : https://prove2.me/submissions/bba78ddd-11c2-4f1e-a7f1-95515d676210

import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRoot
import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootInput
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSquareRootMachine

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : LPSResiduePrime p) :
    lpsResidueY a.q=(SquareRoot.index (a.q-1) a.q (lpsMinusRoot_numeric_exists a):ZMod a.q) := by
  unfold lpsResidueY lpsEffectiveResidueY
  rw [←lpsMinusRoot_pair_index a,Nat.mod_eq_of_lt (SquareRoot.index_lt _ _ _)]
end QEC.Coding.TannerLiftedProduct
