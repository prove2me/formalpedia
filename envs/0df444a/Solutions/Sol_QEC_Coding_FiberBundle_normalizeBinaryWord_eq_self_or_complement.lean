-- Prove2me | solution 1 for QEC.Coding.FiberBundle.normalizeBinaryWord_eq_self_or_complement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:55:29.787147+00:00
-- url     : https://prove2.me/submissions/ae30d94a-28de-4a4d-b314-97eb24cd16bc

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {ι : Type u} [Fintype ι] (x : Word (ZMod 2) ι) :
    normalizeBinaryWord x = x ∨ normalizeBinaryWord x = binaryComplement x := by
  unfold normalizeBinaryWord
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl
end QEC.Coding.FiberBundle
