-- Prove2me | solution 1 for QEC.Coding.FiberBundle.twice_hammingWeight_normalizeBinaryWord_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:18:59.134601+00:00
-- url     : https://prove2.me/submissions/cd6b0a23-0c02-4763-a60a-ce7ecba0f0c4

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_add_hammingWeight_binaryComplement

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {ι : Type u} [Fintype ι] (x : Word (ZMod 2) ι) :
    2 * HammingWeight (normalizeBinaryWord x) ≤ Fintype.card ι := by
  by_cases hx : 2 * HammingWeight x ≤ Fintype.card ι
  · rw [normalizeBinaryWord, if_pos hx]
    exact hx
  · rw [normalizeBinaryWord, if_neg hx]
    have hpartition := hammingWeight_add_hammingWeight_binaryComplement x
    omega
end QEC.Coding.FiberBundle
