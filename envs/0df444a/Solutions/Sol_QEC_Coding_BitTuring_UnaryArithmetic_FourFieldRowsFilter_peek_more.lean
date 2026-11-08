-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.peek_more
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:09:40.16118+00:00
-- url     : https://prove2.me/submissions/35c66009-3eaa-401e-abbc-ab367833066c

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (f:Bool) (h:Option Bool) (I O H C B:List Bool) (a:Bool):
 TM2.step (program P) (cfg P 1 f h (a::I) O H C B)=some (cfg P 2 f (some a) (a::I) O H C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
