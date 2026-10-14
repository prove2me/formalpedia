-- Prove2me | solution 1 for actuarial_c_claim_at_death
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:58:29.014694+00:00
-- url     : https://prove2.me/submissions/5946e955-6e3a-421a-9291-025470e37190

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path

open ActuarialAssurances

theorem solution (h k : ℕ) (v : ℝ) (b : ℕ → ℝ) (hk : k < h) : path h v b k=v^(k+1)*b k := by
  simp only [path, death]
  have hkmem : k ∈ Finset.range h := Finset.mem_range.mpr hk
  rw [Finset.sum_eq_single k]
  · simp [if_pos rfl]
  · intro j _ hne
    simp [Ne.symm hne]
  · intro hnin
    exact absurd hkmem hnin

