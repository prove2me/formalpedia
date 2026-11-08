-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.peek_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:09:41.699672+00:00
-- url     : https://prove2.me/submissions/c8f3c356-daff-4d58-a470-550c22f5d113

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (f:Bool) (h:Option Bool) (O H C B:List Bool) :
 TM2.step (program P) (cfg P 1 f h [] O H C B)=some (cfg P 12 f none [] O H C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
