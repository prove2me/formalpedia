-- Prove2me | solution 1 for QEC.Coding.BitTuring.CountedFlagLoop.halt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:57:01.82859+00:00
-- url     : https://prove2.me/submissions/5e345da1-386d-4641-af11-ff85600a809e

import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Definitions.Def_QEC_Coding_BitTuring_CountedFlagLoop

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.CountedFlagLoop
open Turing StateTransition
variable (A:Machine)
namespace QEC.Coding.BitTuring.CountedFlagLoop
theorem _root_.solution (w:List Bool):halt A w=(machine A).halt w:=rfl
end QEC.Coding.BitTuring.CountedFlagLoop
