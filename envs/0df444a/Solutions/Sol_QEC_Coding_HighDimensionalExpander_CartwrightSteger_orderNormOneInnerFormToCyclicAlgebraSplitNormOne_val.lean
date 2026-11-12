-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormToCyclicAlgebraSplitNormOne_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:50:27.588738+00:00
-- url     : https://prove2.me/submissions/8653776b-9240-4fe4-be52-7c63ed14a45c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    (orderNormOneInnerFormToCyclicAlgebraSplitNormOne P r s :
        (CyclicAlgebra P r)ˣ) =
      orderUnitToCyclicUnit P r
        (orderNormOneInnerFormToOrderUnits P r s) :=
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
