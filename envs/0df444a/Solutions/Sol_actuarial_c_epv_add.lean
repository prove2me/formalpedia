-- Prove2me | solution 1 for actuarial_c_epv_add
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:50.246333+00:00
-- url     : https://prove2.me/submissions/9ad6f527-200f-4b4c-99a5-de3572062e99

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv

open ActuarialAssurances

theorem solution (h : ℕ) (v : ℝ) (b c p : ℕ → ℝ) : epv h v (fun j => b j+c j) p=epv h v b p+epv h v c p := by
  simp only [epv]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  have hpath : path h v (fun j => b j + c j) k = path h v b k + path h v c k := by
    simp only [path, death]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    split_ifs <;> simp [mul_add]
  rw [hpath, mul_add]

