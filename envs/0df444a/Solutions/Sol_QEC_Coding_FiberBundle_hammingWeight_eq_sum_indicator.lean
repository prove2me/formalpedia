-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_eq_sum_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:52:05.630202+00:00
-- url     : https://prove2.me/submissions/3555e8a9-e8a3-4f53-b834-d18cea10cbeb

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
    HammingWeight x = ∑ i : ι, if x i ≠ 0 then 1 else 0 := by
  classical
  rw [HammingWeight, hammingSupport, Finset.card_filter]
end QEC.Coding.FiberBundle
