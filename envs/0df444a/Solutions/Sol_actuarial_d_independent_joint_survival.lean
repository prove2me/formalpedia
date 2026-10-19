-- Prove2me | solution 1 for actuarial_d_independent_joint_survival
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:57:28.108158+00:00
-- url     : https://prove2.me/submissions/904b3e1e-0e01-4678-81b1-0c46fb6f1632

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_independentMass
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_px
import Definitions.Def_actuarial_d_py

open ActuarialJointD

theorem solution (h t : ℕ) (u v : ℕ → ℝ) (hu : (∑ i ∈ Finset.range (h+1), u i) = 1) (hv : (∑ j ∈ Finset.range (h+1), v j) = 1) : pxy h (independentMass u v) t = px h (independentMass u v) t * py h (independentMass u v) t := by
  have hx : px h (independentMass u v) t = ∑ i ∈ Finset.range (h+1), u i * alive i t := by
    simp only [px, expect, independentMass]
    have : ∀ i, ∑ j ∈ Finset.range (h+1), u i * v j * alive i t = u i * alive i t * ∑ j ∈ Finset.range (h+1), v j := by
      intro i; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [this, hv, mul_one]
  have hy : py h (independentMass u v) t = ∑ j ∈ Finset.range (h+1), v j * alive j t := by
    simp only [py, expect, independentMass]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ i ∈ Finset.range (h+1), u i * v j * alive j t = v j * alive j t * ∑ i ∈ Finset.range (h+1), u i := by
      intro j; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [this, hu, mul_one]
  rw [hx, hy, Finset.sum_mul_sum]
  simp only [pxy, expect, independentMass, both]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
