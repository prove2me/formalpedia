-- Prove2me | solution 1 for ThreeSum.BruteTripleIndex.code_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:08.057176+00:00
-- url     : https://prove2.me/submissions/6995605e-9cb0-4837-859e-34aff37908d4

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSum_BruteTripleIndex

set_option autoImplicit false
open ThreeSum ThreeSum.BruteTripleIndex
namespace ThreeSum.BruteTripleIndex
theorem _root_.solution {n : ℕ} (i j k : Fin n) : code i j k < n^3 := by
  have hpair : i.val*n+j.val < n*n := by
    calc
      _ < i.val*n+n := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*n := by ring
      _ ≤ n*n := Nat.mul_le_mul_right n (by omega)
  calc
    code i j k < (i.val*n+j.val)*n+n := Nat.add_lt_add_left k.isLt _
    _ = (i.val*n+j.val+1)*n := by ring
    _ ≤ (n*n)*n := Nat.mul_le_mul_right n (by omega)
    _ = n^3 := by ring
end ThreeSum.BruteTripleIndex
