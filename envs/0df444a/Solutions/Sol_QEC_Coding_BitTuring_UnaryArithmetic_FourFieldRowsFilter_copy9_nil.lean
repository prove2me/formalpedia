-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.copy9_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:10:05.766205+00:00
-- url     : https://prove2.me/submissions/d5c99769-6a37-4e6c-b048-59f22336638f

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I H C B:List Bool) :
 TM2.step (program P) (cfg P 9 f h I [] H C B)=some (cfg P 10 f none I [] H C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead,Ne.symm hio]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
