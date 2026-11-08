-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.restore11_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:10:39.93701+00:00
-- url     : https://prove2.me/submissions/f4700e1e-6d8e-4707-b1ac-4b4aa2d69e83

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (f:Bool) (h:Option Bool) (I O C B:List Bool) :
 TM2.step (program P) (cfg P 11 f h I O [] C B)=some (cfg P 0 false none I O [] C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
