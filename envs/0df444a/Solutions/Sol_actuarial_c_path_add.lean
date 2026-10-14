-- Prove2me | solution 1 for actuarial_c_path_add
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:50.942319+00:00
-- url     : https://prove2.me/submissions/694a7f2f-ae0c-417f-9fed-7a5cebe37c4b

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path

open ActuarialAssurances

theorem solution (h k : ℕ) (v : ℝ) (b c : ℕ → ℝ) : path h v (fun j => b j+c j) k=path h v b k+path h v c k := by
  simp only [path, death]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  split_ifs <;> simp [mul_add]
