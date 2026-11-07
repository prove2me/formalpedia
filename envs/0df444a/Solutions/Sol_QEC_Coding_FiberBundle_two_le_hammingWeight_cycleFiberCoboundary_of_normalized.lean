-- Prove2me | solution 1 for QEC.Coding.FiberBundle.two_le_hammingWeight_cycleFiberCoboundary_of_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:31:01.147204+00:00
-- url     : https://prove2.me/submissions/c7f91b0a-576f-4d78-9606-db230ac361d6

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_two_le_hammingWeight_cycleFiberCoboundary
import Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberCoboundary_ne_zero_of_normalized

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (f : Word (ZMod 2) (ZMod n))
    (hf : f ≠ 0)
    (hhalf : 2 * HammingWeight f ≤ Fintype.card (ZMod n)) :
    2 ≤ HammingWeight (cycleFiberCoboundary n f) :=
  two_le_hammingWeight_cycleFiberCoboundary n hn f
    (cycleFiberCoboundary_ne_zero_of_normalized n hn f hf hhalf)
end QEC.Coding.FiberBundle
