-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_verticalComponent_eq_sum_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:54:17.007769+00:00
-- url     : https://prove2.me/submissions/b67af2b7-089d-4ce3-ba12-946d68ac8ec7

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
    [Fintype baseZero] [Fintype fiberOne]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    HammingWeight (verticalComponent x) =
      ∑ a : baseZero, HammingWeight (verticalFiber x a) := by
  classical
  rw [hammingWeight_eq_sum_indicator, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [hammingWeight_eq_sum_indicator]
  rfl
end QEC.Coding.FiberBundle
