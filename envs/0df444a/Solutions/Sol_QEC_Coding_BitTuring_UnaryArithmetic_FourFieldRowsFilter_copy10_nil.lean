-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.copy10_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:10:32.693234+00:00
-- url     : https://prove2.me/submissions/917ce36d-3a24-4a70-b2db-7ac817bcad24

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (f:Bool) (h:Option Bool) (I O H C:List Bool) :
 TM2.step (program P) (cfg P 10 f h I O H C [])=some (cfg P 11 f none I O H C []):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
