-- Prove2me | solution 1 for RevisitXor.claim_7_1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:45:54.443332+00:00
-- url     : https://prove2.me/submissions/4be43611-66d2-48ee-95c3-55f613677424

import Definitions.Def_RevisitXor_wEdge

open RevisitXor in
theorem solution {m : ℕ} (h : Cube m × Cube m → ZMod 2) (x y : Cube m) :
    |wDir h x y| ≤ 1 := by
  unfold wDir
  have hc : (0 : ℝ) < (Fintype.card (Cube m) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [abs_mul, abs_inv, abs_of_pos hc, inv_mul_le_iff₀ hc, mul_one]
  calc |∑ z : Cube m, sgn (z ⬝ᵥ y + h (z, x))|
      ≤ ∑ z : Cube m, |sgn (z ⬝ᵥ y + h (z, x))| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _z : Cube m, (1 : ℝ) := by
        apply Finset.sum_congr rfl; intro z _
        simp [sgn, abs_pow]
    _ = (Fintype.card (Cube m) : ℝ) := by simp
