-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.fullyGoodBaseFailureBound_toReal_lt_one_tenth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:00:02.278127+00:00
-- url     : https://prove2.me/submissions/228d6eda-4168-4d51-a245-df1eec4aa556

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_fullyGoodBaseFailureBound_toReal
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_fullyGoodBaseFailureBoundReal_lt_one_tenth

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat)
    (hr : 500 ≤ r) (hFive : 5 ∣ r)
    (hDegree :
      (14 * r : Real) * Real.exp (-(Delta : Real) / 40000) <
        1 / 100)
    (hRank :
      (3 * r : Real) * Real.exp (-(Delta : Real) / 2) <
        1 / 200)
    (hDistance :
      (4 * r : Real) *
          Real.exp (-(3 : Real) * Delta / 28) <
        1 / 200)
    (hExpansion :
      (3 * r : Real) * Real.exp (-(Delta : Real) / 1000) <
        1 / 200) :
    (fullyGoodBaseFailureBound r Delta).toReal < 1 / 10 := by
  rw [fullyGoodBaseFailureBound_toReal]
  exact fullyGoodBaseFailureBoundReal_lt_one_tenth
    r Delta hr hFive hDegree hRank hDistance hExpansion
end QEC.Coding.FiberBundle.RandomPartition
