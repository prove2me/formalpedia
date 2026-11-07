-- Prove2me | solution 1 for QEC.Coding.FiberBundle.zmodFinEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:32:23.716395+00:00
-- url     : https://prove2.me/submissions/4af728d1-93da-4ca6-8162-f4d5f5b13c33

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (n : Nat) [NeZero n] (k : Fin n) :
    ZMod.finEquiv n k = (k.val : ZMod n) := by
  apply ZMod.val_injective n
  rw [ZMod.val_natCast_of_lt k.isLt]
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl
end QEC.Coding.FiberBundle
