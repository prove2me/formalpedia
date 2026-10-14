-- Prove2me | solution 1 for actuarial_c_delay_path_factor
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:54:04.753418+00:00
-- url     : https://prove2.me/submissions/7eb8624e-0d32-4312-9d44-343ebe769630

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_delayPath

open ActuarialAssurances

theorem solution (h lag k : ℕ) (v : ℝ) (b : ℕ → ℝ) : delayPath h lag v b k=v^lag*path h v b k := by
  simp only [delayPath, path]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp [pow_add, mul_assoc, mul_left_comm, mul_comm]

