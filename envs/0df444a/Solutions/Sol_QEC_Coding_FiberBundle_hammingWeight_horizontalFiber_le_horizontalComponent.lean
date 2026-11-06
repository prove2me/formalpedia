-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_horizontalFiber_le_horizontalComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:56:30.998579+00:00
-- url     : https://prove2.me/submissions/ca88c765-ddda-4641-9217-403e745025e8

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_eq_sum_fibers

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseOne] [Fintype fiberZero]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne))
    (b : baseOne) :
    HammingWeight (horizontalFiber x b) ≤
      HammingWeight (horizontalComponent x) := by
  rw [hammingWeight_horizontalComponent_eq_sum_fibers]
  exact Finset.single_le_sum
    (f := fun b' => HammingWeight (horizontalFiber x b'))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
end QEC.Coding.FiberBundle
