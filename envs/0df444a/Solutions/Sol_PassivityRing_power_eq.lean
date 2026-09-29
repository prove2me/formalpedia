-- Prove2me | solution 1 for PassivityRing.power_eq
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-23T22:01:32.145483+00:00
-- url     : https://prove2.me/submissions/5a1f9c07-4448-4238-ad67-c29d789f4880

import Mathlib
import Definitions.Def_PassivityRing_power

open Matrix BigOperators

open PassivityRing

theorem solution (N d : ℕ) [NeZero N]
    (W : Fin N → Matrix (Fin d) (Fin d) ℝ) (v : Fin N → (Fin d → ℝ)) :
    power N d W v = ∑ i : Fin N, v i ⬝ᵥ ((W i - (W i)ᵀ) *ᵥ v (i + 1)) := by
  unfold power
  have key : ∑ i : Fin N, v i ⬝ᵥ (W (i - 1) *ᵥ v (i - 1))
      = ∑ i : Fin N, v i ⬝ᵥ ((W i)ᵀ *ᵥ v (i + 1)) := by
    rw [← Equiv.sum_comp (Equiv.addRight (1 : Fin N))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [dotProduct_mulVec (v j), vecMul_transpose, dotProduct_comm]
  simp only [dotProduct_sub, Finset.sum_sub_distrib, sub_mulVec, key]
