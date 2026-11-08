-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.hho20_degreeScale_le_two_baseScale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:56:07.481148+00:00
-- url     : https://prove2.me/submissions/f6bf1d62-cf5e-474d-bc71-e01d2a851ac7

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hho20_degreeScale_le_two_fiberCells

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (s : Nat) (hs : 200 ≤ s) :
    hho20DegreeScale s ≤ 2 * hho20BaseScale s := by
  exact (hho20_degreeScale_le_two_fiberCells s hs).trans
    (Nat.mul_le_mul_left 2
      (Nat.le_of_lt (hho20_fiberCells_lt_baseScale s (by omega))))
end QEC.Coding.FiberBundle.RandomPartition
