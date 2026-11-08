-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.million_mul_le_four_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:37:17.440245+00:00
-- url     : https://prove2.me/submissions/968bacfb-6a1e-4d9a-bd63-bfd828f244cb

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (s : Nat) (hs : 20 ≤ s) :
    1000000 * s ≤ 4 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      calc
        1000000 * (n + 1) ≤ 4 * (1000000 * n) := by omega
        _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ n * 4 := by ring
end QEC.Coding.FiberBundle.RandomPartition
