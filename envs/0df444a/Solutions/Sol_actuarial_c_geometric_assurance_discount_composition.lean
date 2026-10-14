-- Prove2me | solution 1 for actuarial_c_geometric_assurance_discount_composition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:18:20.763974+00:00
-- url     : https://prove2.me/submissions/89db7ca7-06be-41e1-ad6f-c3ee5a102342

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_geom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances

theorem solution (h : ℕ) (v g : ℝ) (p : ℕ → ℝ) :
    epv h v (geom g) p =
      v * (∑ j ∈ Finset.range h, (v*g)^j * p j) := by
  unfold epv path geom
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hjmem : j ∈ Finset.range (h + 1) := by
    have hjh : j < h := Finset.mem_range.mp hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_lt hjh)
  calc
    (∑ k ∈ Finset.range (h+1),
      p k * (v^(j+1) * g^j * death k j)) =
      ∑ k ∈ Finset.range (h+1),
        if k = j then p k * (v^(j+1) * g^j) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hkj : k = j <;> simp [death, hkj]
    _ = p j * (v^(j+1) * g^j) := by simp [hjmem]
    _ = v * ((v*g)^j * p j) := by
      rw [mul_pow, pow_succ]
      ring
