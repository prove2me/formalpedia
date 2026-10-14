-- Prove2me | solution 1 for actuarial_c_mass_cohort_decrement
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:04:57.122186+00:00
-- url     : https://prove2.me/submissions/36c47bfd-df7a-4334-8a95-74458824a79c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_massCohort

open ActuarialAssurances

theorem solution (h j : ℕ) (p : ℕ → ℝ) (hj : j < h) : massCohort h p j-massCohort h p (j+1)=p j := by
  simp only [massCohort, surv, alive]
  rw [← Finset.sum_sub_distrib]
  have hmem : j ∈ Finset.range (h + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_lt hj)
  rw [Finset.sum_eq_single j]
  · have h1 : ¬ j + 1 ≤ j := by omega
    simp [le_rfl, h1]
  · intro k hk hne
    by_cases hkj : j ≤ k <;> by_cases hkj1 : j + 1 ≤ k <;> simp [hkj, hkj1]
    · omega
    · omega
  · intro hnin
    exact absurd hmem hnin

