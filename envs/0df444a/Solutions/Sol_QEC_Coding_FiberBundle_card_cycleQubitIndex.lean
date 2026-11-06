-- Prove2me | solution 1 for QEC.Coding.FiberBundle.card_cycleQubitIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:51:11.863268+00:00
-- url     : https://prove2.me/submissions/4bc8a39a-9bce-4eb3-b7aa-b5e84b4ef5d5

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_FiberBundle_Core
import Theorems.Thm_QEC_Coding_FiberBundle_card_qubitIndex

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {baseZero baseOne : Type*}
    [Fintype baseZero] [Fintype baseOne]
    (n : Nat) [NeZero n] :
    Fintype.card
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n)) =
      Fintype.card baseOne * n + Fintype.card baseZero * n := by
  rw [card_qubitIndex, ZMod.card n]
end QEC.Coding.FiberBundle
