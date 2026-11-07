-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_eq_horizontal_add_vertical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:56:04.629715+00:00
-- url     : https://prove2.me/submissions/0b16e3f0-51e8-43cf-b053-6e36ebd3241d

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_eq_sum_indicator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [Fintype baseOne]
    [Fintype fiberZero] [Fintype fiberOne]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    HammingWeight x =
      HammingWeight (horizontalComponent x) +
        HammingWeight (verticalComponent x) := by
  classical
  rw [hammingWeight_eq_sum_indicator, Fintype.sum_sum_type,
    hammingWeight_eq_sum_indicator, hammingWeight_eq_sum_indicator]
  rfl
end QEC.Coding.FiberBundle
