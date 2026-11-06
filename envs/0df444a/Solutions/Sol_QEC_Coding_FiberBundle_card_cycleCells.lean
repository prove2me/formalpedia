-- Prove2me | solution 1 for QEC.Coding.FiberBundle.card_cycleCells
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:51:11.067717+00:00
-- url     : https://prove2.me/submissions/bde403c7-c5c3-43d4-9262-d8837f972bb1

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_FiberBundle_Core

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution (n : Nat) [NeZero n] :
    Fintype.card (ZMod n) = n :=
  ZMod.card n
end QEC.Coding.FiberBundle
