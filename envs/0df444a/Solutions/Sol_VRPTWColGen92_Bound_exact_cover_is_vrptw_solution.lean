-- Prove2me | solution 1 for VRPTWColGen92.Bound.exact_cover_is_vrptw_solution
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:15:11.922631+00:00
-- url     : https://prove2.me/submissions/4bb1b5a3-5e58-41f0-8572-e5300bc34dd6

import Mathlib
import Definitions.Def_VRPTWColGen92_Bound_Network
import Definitions.Def_VRPTWColGen92_Bound_CoveringLP

open VRPTWColGen92.Bound
theorem solution {n : ℕ} (I : Instance n)
    (z : LPPoint n) (hz : LPFeasible I {p | IsPath I p} z)
    (hint : ∀ p, ∃ m : ℕ, z.x p = m)
    (hexact : ∀ i : Fin (n + 1), i ≠ 0 →
      ∑ p ∈ z.x.support, (p.count i : ℝ) * z.x p = 1) :
    IsVRPTWSolution I z.x.support ∧ solCost I z.x.support = objective I z := by
  classical
  have hxge : ∀ p ∈ z.x.support, 1 ≤ z.x p := by
    intro p hp
    obtain ⟨m, hm⟩ := hint p
    have hmpos : 0 < m := by
      have : z.x p ≠ 0 := Finsupp.mem_support_iff.mp hp
      have : m ≠ 0 := by intro h; simp [h] at hm; exact this hm
      omega
    rw [hm]
    exact_mod_cast hmpos
  have hbound : ∀ p ∈ z.x.support, ∀ i, i ≠ 0 →
      (p.count i : ℝ) * z.x p ≤ 1 := by
    intro p hp i hi
    rw [← hexact i hi]
    exact Finset.single_le_sum (fun q _ => mul_nonneg (Nat.cast_nonneg _) (hz.2.1 q)) hp
  have hcount : ∀ p ∈ z.x.support, ∀ i, p.count i ≤ 1 := by
    intro p hp i
    by_cases hi : i = 0
    · subst i
      have hnot := (hz.1 p hp).2.1
      simp [List.count_eq_zero.mpr hnot]
    · have hb := hbound p hp i hi
      have hg := hxge p hp
      have hc : (0 : ℝ) ≤ p.count i := Nat.cast_nonneg _
      have : (p.count i : ℝ) ≤ 1 := by nlinarith
      exact_mod_cast this
  have hxone : ∀ p ∈ z.x.support, z.x p = 1 := by
    intro p hp
    have hpath := hz.1 p hp
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil p hpath.1
    have hi0 : i ≠ 0 := by intro h; subst i; exact hpath.2.1 hi
    have hc : p.count i = 1 := by
      have hpcount : 0 < p.count i := List.count_pos_iff.mpr hi
      have hcle := hcount p hp i
      omega
    have hb := hbound p hp i hi0
    rw [hc] at hb
    simp only [Nat.cast_one, one_mul] at hb
    exact le_antisymm hb (hxge p hp)
  constructor
  · constructor
    · intro p hp
      refine ⟨hz.1 p hp, ?_⟩
      exact List.nodup_iff_count_le_one.mpr (hcount p hp)
    · intro i hi
      rw [← hexact i hi]
      apply Finset.sum_congr rfl
      intro p hp
      rw [hxone p hp, mul_one]
  · unfold solCost objective
    apply Finset.sum_congr rfl
    intro p hp
    rw [hxone p hp, mul_one]



#print axioms solution
