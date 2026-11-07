-- Prove2me | solution 1 for QEC.Coding.BitTuring.CountedFlagLoop.start_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:57:11.00461+00:00
-- url     : https://prove2.me/submissions/90ec3d52-8275-43ef-9360-78394a3293d0

import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Definitions.Def_QEC_Coding_BitTuring_CountedFlagLoop

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.CountedFlagLoop
open Turing StateTransition
variable (A:Machine)
namespace QEC.Coding.BitTuring.CountedFlagLoop
theorem _root_.solution (x:List Bool):start A x []=(machine A).init x:=by
 simp only [start,embed,liftCfg,Machine.init,FlagLoop.machine,machine,Option.elim_some,id_eq]
 congr 1
 funext k;cases k with
 | inl k=>by_cases h:k=.inl A.input <;> simp [tapes,Function.update,h]
 | inr k=>simp [tapes,Function.update]
end QEC.Coding.BitTuring.CountedFlagLoop
