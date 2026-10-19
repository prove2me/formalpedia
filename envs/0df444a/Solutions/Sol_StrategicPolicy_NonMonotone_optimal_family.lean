-- Prove2me | solution 1 for StrategicPolicy.NonMonotone.optimal_family
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-18T02:00:53.340169+00:00
-- url     : https://prove2.me/submissions/fb1f3fda-8b60-4080-a03b-aa3b5d02d087

import Mathlib
import Definitions.Def_StrategicPolicy_NonMonotone_Setting
import Definitions.Def_StrategicPolicy_NonMonotone_Example

set_option autoImplicit false

namespace StrategicPolicy.NonMonotone.Sol_StrategicPolicy_NonMonotone_optimal_family

open StrategicPolicy.NonMonotone

/-- The `MonotoneBinary` best response lies in `bestOutcome`. -/
theorem mb_br_mem (ρ : Fin 3 → ℝ) (i : Fin 3) :
    StrategicPolicy.MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ i ∈
      StrategicPolicy.MonotoneBinary.bestOutcome StrategicPolicy.NonMonotone.c
        StrategicPolicy.NonMonotone.q ρ i :=
  Finset.min'_mem _ _

/-- The `NonMonotone` best response lies in `preferredSet`. -/
theorem nm_br_mem (ρ : Fin 3 → ℝ) (i : Fin 3) :
    StrategicPolicy.NonMonotone.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ i ∈
      StrategicPolicy.NonMonotone.preferredSet StrategicPolicy.NonMonotone.c
        StrategicPolicy.NonMonotone.q ρ i :=
  Finset.min'_mem _ _

theorem mb_br_spec (ρ : Fin 3 → ℝ) (i : Fin 3) :
    (∀ l, ρ l - StrategicPolicy.NonMonotone.c i l ≤
      ρ (StrategicPolicy.MonotoneBinary.br StrategicPolicy.NonMonotone.c
          StrategicPolicy.NonMonotone.q ρ i) -
        StrategicPolicy.NonMonotone.c i
          (StrategicPolicy.MonotoneBinary.br StrategicPolicy.NonMonotone.c
            StrategicPolicy.NonMonotone.q ρ i)) ∧
    (∀ l, l ∈ StrategicPolicy.MonotoneBinary.argmax StrategicPolicy.NonMonotone.c ρ i →
      StrategicPolicy.NonMonotone.q l ≤ StrategicPolicy.NonMonotone.q
        (StrategicPolicy.MonotoneBinary.br StrategicPolicy.NonMonotone.c
          StrategicPolicy.NonMonotone.q ρ i)) := by
  have h := mb_br_mem ρ i
  unfold StrategicPolicy.MonotoneBinary.bestOutcome at h
  rw [Finset.mem_filter] at h
  obtain ⟨h1, h2⟩ := h
  unfold StrategicPolicy.MonotoneBinary.argmax at h1
  rw [Finset.mem_filter] at h1
  exact ⟨h1.2, h2⟩

theorem nm_br_spec (ρ : Fin 3 → ℝ) (i : Fin 3) :
    (∀ l, l ∈ StrategicPolicy.NonMonotone.bestSet StrategicPolicy.NonMonotone.c ρ i →
      StrategicPolicy.NonMonotone.q l ≤ StrategicPolicy.NonMonotone.q
        (StrategicPolicy.NonMonotone.br StrategicPolicy.NonMonotone.c
          StrategicPolicy.NonMonotone.q ρ i)) := by
  have h := nm_br_mem ρ i
  unfold StrategicPolicy.NonMonotone.preferredSet at h
  rw [Finset.mem_filter] at h
  exact h.2

theorem q_vals : StrategicPolicy.NonMonotone.q 0 = 1 ∧ StrategicPolicy.NonMonotone.q 1 = 7 / 10 ∧
    StrategicPolicy.NonMonotone.q 2 = 2 / 5 := by
  simp [StrategicPolicy.NonMonotone.q]

theorem p_vals : StrategicPolicy.NonMonotone.p 0 = 1 / 10 ∧ StrategicPolicy.NonMonotone.p 1 = 2 / 5 ∧
    StrategicPolicy.NonMonotone.p 2 = 1 / 2 := by
  simp [StrategicPolicy.NonMonotone.p]

theorem γ_val : StrategicPolicy.NonMonotone.γ = 1 / 10 := rfl

/-- If `q 0 ≤ q k` then `k = 0`. -/
theorem eq_zero_of_q (k : Fin 3) (hk : StrategicPolicy.NonMonotone.q 0 ≤ StrategicPolicy.NonMonotone.q k) :
    k = 0 := by
  obtain ⟨hq0, hq1, hq2⟩ := q_vals
  fin_cases k
  · rfl
  · simp only [Fin.mk_one, hq0, hq1] at hk; norm_num at hk
  · simp only [Fin.reduceFinMk, hq0, hq2] at hk; norm_num at hk

/-- (L1) Feature 2 never moves. -/
theorem mb_br_two (ρ : Fin 3 → ℝ) (hρ : ρ ∈ StrategicPolicy.MonotoneBinary.Policies 3) :
    StrategicPolicy.MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ 2 = 2 := by
  have h := (mb_br_spec ρ 2).1 2
  have hρ2 := (hρ 2).1
  have hρ0 := (hρ 0).2
  have hρ1 := (hρ 1).2
  generalize StrategicPolicy.MonotoneBinary.br StrategicPolicy.NonMonotone.c
    StrategicPolicy.NonMonotone.q ρ 2 = k at h ⊢
  fin_cases k
  · simp [StrategicPolicy.NonMonotone.c] at h; linarith
  · simp [StrategicPolicy.NonMonotone.c] at h; linarith
  · rfl

/-- Each weighted outcome is at most `9/10`. -/
theorem qterm_le (ρ : Fin 3 → ℝ) (hρ : ρ ∈ StrategicPolicy.MonotoneBinary.Policies 3) (k : Fin 3) :
    (StrategicPolicy.NonMonotone.q k - StrategicPolicy.NonMonotone.γ) * ρ k ≤ 9 / 10 := by
  obtain ⟨hq0, hq1, hq2⟩ := q_vals
  have h0 := (hρ k).1
  have h1 := (hρ k).2
  rw [γ_val]
  fin_cases k
  · simp only [Fin.zero_eta, hq0] at h0 h1 ⊢; nlinarith
  · simp only [Fin.mk_one, hq1] at h0 h1 ⊢; nlinarith
  · simp only [Fin.reduceFinMk, hq2] at h0 h1 ⊢; nlinarith

/-- (L2) Upper bound on the utility. -/
theorem u_le (ρ : Fin 3 → ℝ) (hρ : ρ ∈ StrategicPolicy.MonotoneBinary.Policies 3) :
    StrategicPolicy.MonotoneBinary.u StrategicPolicy.NonMonotone.p StrategicPolicy.NonMonotone.q
      StrategicPolicy.NonMonotone.γ StrategicPolicy.NonMonotone.c ρ ≤ 6 / 10 := by
  obtain ⟨hp0, hp1, hp2⟩ := p_vals
  obtain ⟨_, _, hq2⟩ := q_vals
  have e : StrategicPolicy.MonotoneBinary.u StrategicPolicy.NonMonotone.p StrategicPolicy.NonMonotone.q
      StrategicPolicy.NonMonotone.γ StrategicPolicy.NonMonotone.c ρ =
      StrategicPolicy.NonMonotone.p 0 *
        ((StrategicPolicy.NonMonotone.q (StrategicPolicy.MonotoneBinary.br StrategicPolicy.NonMonotone.c
            StrategicPolicy.NonMonotone.q ρ 0) - StrategicPolicy.NonMonotone.γ) *
          ρ (StrategicPolicy.MonotoneBinary.br StrategicPolicy.NonMonotone.c
            StrategicPolicy.NonMonotone.q ρ 0)) +
      StrategicPolicy.NonMonotone.p 1 *
        ((StrategicPolicy.NonMonotone.q (StrategicPolicy.MonotoneBinary.br StrategicPolicy.NonMonotone.c
            StrategicPolicy.NonMonotone.q ρ 1) - StrategicPolicy.NonMonotone.γ) *
          ρ (StrategicPolicy.MonotoneBinary.br StrategicPolicy.NonMonotone.c
            StrategicPolicy.NonMonotone.q ρ 1)) +
      StrategicPolicy.NonMonotone.p 2 *
        ((StrategicPolicy.NonMonotone.q 2 - StrategicPolicy.NonMonotone.γ) * ρ 2) := by
    unfold StrategicPolicy.MonotoneBinary.u
    rw [Fin.sum_univ_three, mb_br_two ρ hρ]
    ring
  have t0 := qterm_le ρ hρ (StrategicPolicy.MonotoneBinary.br StrategicPolicy.NonMonotone.c
    StrategicPolicy.NonMonotone.q ρ 0)
  have t1 := qterm_le ρ hρ (StrategicPolicy.MonotoneBinary.br StrategicPolicy.NonMonotone.c
    StrategicPolicy.NonMonotone.q ρ 1)
  have t2 : (StrategicPolicy.NonMonotone.q 2 - StrategicPolicy.NonMonotone.γ) * ρ 2 ≤ 3 / 10 := by
    rw [hq2, γ_val]
    have := (hρ 2).2
    nlinarith
  rw [e, hp0, hp1, hp2]
  linarith

/-- (L3) For the printed family, features `0` and `1` best-respond with `0` (`MonotoneBinary.br`). -/
theorem mb_br_eq_zero (π : Fin 3 → ℝ) (hπ : π ∈ StrategicPolicy.MonotoneBinary.Policies 3)
    (h0 : π 0 = 1) (h1 : π 1 ≤ 7 / 10) (h2 : π 2 = 1) (i : Fin 3) (hi : i ≠ 2) :
    StrategicPolicy.MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q π i = 0 := by
  have hmem : (0 : Fin 3) ∈ StrategicPolicy.MonotoneBinary.argmax StrategicPolicy.NonMonotone.c π i := by
    unfold StrategicPolicy.MonotoneBinary.argmax
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro l
    have := (hπ 1).1
    fin_cases i <;> fin_cases l <;> simp [StrategicPolicy.NonMonotone.c, h0, h2] at hi ⊢ <;> linarith
  exact eq_zero_of_q _ ((mb_br_spec π i).2 0 hmem)

/-- (L3') The same for `NonMonotone.br` at feature `1`. -/
theorem nm_br_one_eq_zero (π : Fin 3 → ℝ) (hπ : π ∈ StrategicPolicy.MonotoneBinary.Policies 3)
    (h0 : π 0 = 1) (h1 : π 1 ≤ 7 / 10) (h2 : π 2 = 1) :
    StrategicPolicy.NonMonotone.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q π 1 = 0 := by
  have hmem : (0 : Fin 3) ∈ StrategicPolicy.NonMonotone.bestSet StrategicPolicy.NonMonotone.c π 1 := by
    unfold StrategicPolicy.NonMonotone.bestSet
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro l
    have := (hπ 1).1
    fin_cases l <;> simp [StrategicPolicy.NonMonotone.c, h0, h2] <;> linarith
  exact eq_zero_of_q _ (nm_br_spec π 1 0 hmem)

/-- The utility of the printed family equals `6/10`. -/
theorem u_eq (π : Fin 3 → ℝ) (hπ : π ∈ StrategicPolicy.MonotoneBinary.Policies 3)
    (h0 : π 0 = 1) (h1 : π 1 ≤ 7 / 10) (h2 : π 2 = 1) :
    StrategicPolicy.MonotoneBinary.u StrategicPolicy.NonMonotone.p StrategicPolicy.NonMonotone.q
      StrategicPolicy.NonMonotone.γ StrategicPolicy.NonMonotone.c π = 6 / 10 := by
  obtain ⟨hp0, hp1, hp2⟩ := p_vals
  obtain ⟨hq0, _, hq2⟩ := q_vals
  unfold StrategicPolicy.MonotoneBinary.u
  rw [Fin.sum_univ_three, mb_br_two π hπ, mb_br_eq_zero π hπ h0 h1 h2 0 (by decide),
    mb_br_eq_zero π hπ h0 h1 h2 1 (by decide), hp0, hp1, hp2, hq0, hq2, γ_val, h0, h2]
  norm_num

end StrategicPolicy.NonMonotone.Sol_StrategicPolicy_NonMonotone_optimal_family

open StrategicPolicy.NonMonotone in
theorem solution (π : Fin 3 → ℝ) (hπ : π ∈ StrategicPolicy.MonotoneBinary.Policies 3)
    (h0 : π 0 = 1) (h1 : π 1 ≤ 7 / 10) (h2 : π 2 = 1) :
    IsMaxOn (StrategicPolicy.MonotoneBinary.u StrategicPolicy.NonMonotone.p StrategicPolicy.NonMonotone.q
        StrategicPolicy.NonMonotone.γ StrategicPolicy.NonMonotone.c)
      (StrategicPolicy.MonotoneBinary.Policies 3) π ∧
    StrategicPolicy.NonMonotone.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q π 1 = 0 := by
  refine ⟨?_, StrategicPolicy.NonMonotone.Sol_StrategicPolicy_NonMonotone_optimal_family.nm_br_one_eq_zero
    π hπ h0 h1 h2⟩
  rw [isMaxOn_iff]
  intro ρ hρ
  rw [StrategicPolicy.NonMonotone.Sol_StrategicPolicy_NonMonotone_optimal_family.u_eq π hπ h0 h1 h2]
  exact StrategicPolicy.NonMonotone.Sol_StrategicPolicy_NonMonotone_optimal_family.u_le ρ hρ
