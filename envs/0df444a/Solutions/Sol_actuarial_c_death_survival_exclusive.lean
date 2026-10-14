-- Prove2me | solution 1 for actuarial_c_death_survival_exclusive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:51.616977+00:00
-- url     : https://prove2.me/submissions/935a564e-8c17-4c40-af23-f61316f6e1f1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death

open ActuarialAssurances

theorem solution (k i j : ℕ) (hij : i < j) : death k i*alive k j=0 := by
  unfold death alive
  by_cases hk : k = i
  · have hji : ¬ j ≤ i := not_le_of_gt hij
    simp [hk, hji]
  · simp [hk]
