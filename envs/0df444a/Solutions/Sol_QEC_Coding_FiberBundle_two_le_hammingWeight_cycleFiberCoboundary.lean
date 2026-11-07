-- Prove2me | solution 1 for QEC.Coding.FiberBundle.two_le_hammingWeight_cycleFiberCoboundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:28:11.286115+00:00
-- url     : https://prove2.me/submissions/16377abe-8b8f-4126-9def-0a21398f16d4

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_two_le_hammingWeight_of_sum_eq_zero_of_ne_zero
import Theorems.Thm_QEC_Coding_FiberBundle_sum_cycleFiberCoboundary_eq_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (f : Word (ZMod 2) (ZMod n))
    (hf : cycleFiberCoboundary n f ≠ 0) :
    2 ≤ HammingWeight (cycleFiberCoboundary n f) :=
  two_le_hammingWeight_of_sum_eq_zero_of_ne_zero
    (cycleFiberCoboundary n f)
    (sum_cycleFiberCoboundary_eq_zero n hn f)
    hf
end QEC.Coding.FiberBundle
