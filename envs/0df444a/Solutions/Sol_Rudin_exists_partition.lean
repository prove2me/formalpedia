-- Prove2me | solution 1 for Rudin.exists_partition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T00:03:39.933321+00:00
-- url     : https://prove2.me/submissions/7cd05864-f8d7-4f7d-9aeb-a27bd768b294

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

theorem solution {a b : ℝ} (hab : a ≤ b) :
    Nonempty (Rudin.Partition a b) := by
  refine ⟨{
    n := 1
    x := fun i => if i = 0 then a else b
    first := by simp
    last := by simp
    mono := ?_ }⟩
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  simpa using hab
