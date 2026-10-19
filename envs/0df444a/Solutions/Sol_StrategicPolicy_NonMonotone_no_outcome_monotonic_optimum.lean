-- Prove2me | solution 1 for StrategicPolicy.NonMonotone.no_outcome_monotonic_optimum
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-18T02:02:17.869903+00:00
-- url     : https://prove2.me/submissions/ba62ee3c-8ac8-44f8-9b8b-a58423738ad2

import Mathlib
import Definitions.Def_StrategicPolicy_NonMonotone_Setting
import Definitions.Def_StrategicPolicy_NonMonotone_Example

set_option autoImplicit false

namespace StrategicPolicy.NonMonotone.Sol_StrategicPolicy_NonMonotone_no_outcome_monotonic_optimum

open StrategicPolicy.NonMonotone

/-- The best response lies in the outcome-refined set of benefit maximizers. -/
theorem br_mem (ρ : Fin 3 → ℝ) (i : Fin 3) :
    MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ i ∈
      MonotoneBinary.bestOutcome StrategicPolicy.NonMonotone.c
        StrategicPolicy.NonMonotone.q ρ i := by
  unfold MonotoneBinary.br
  exact Finset.min'_mem _ _

/-- Benefit-maximization property of the best response. -/
theorem br_argmax (ρ : Fin 3 → ℝ) (i l : Fin 3) :
    ρ l - StrategicPolicy.NonMonotone.c i l ≤
      ρ (MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ i) -
        StrategicPolicy.NonMonotone.c i
          (MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ i) := by
  have h := br_mem ρ i
  unfold MonotoneBinary.bestOutcome at h
  have h1 := (Finset.mem_filter.mp h).1
  unfold MonotoneBinary.argmax at h1
  exact (Finset.mem_filter.mp h1).2 l

/-- If `0` maximizes benefit for type `i`, the best response is `0` (outcome tie-break). -/
theorem br_eq_zero (ρ : Fin 3 → ℝ) (i : Fin 3)
    (h0 : (0 : Fin 3) ∈ MonotoneBinary.argmax StrategicPolicy.NonMonotone.c ρ i) :
    MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ i = 0 := by
  have h := br_mem ρ i
  unfold MonotoneBinary.bestOutcome at h
  have h2 := (Finset.mem_filter.mp h).2 0 h0
  generalize MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ i
    = b at h2 ⊢
  fin_cases b
  · rfl
  · simp [StrategicPolicy.NonMonotone.q] at h2
    norm_num at h2
  · simp [StrategicPolicy.NonMonotone.q] at h2
    norm_num at h2

/-- (L1) Type `2` never moves. -/
theorem br_two (ρ : Fin 3 → ℝ) (hρ : ρ ∈ MonotoneBinary.Policies 3) :
    MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ 2 = 2 := by
  have h := br_argmax ρ 2 2
  have h0 := (hρ 0).1
  have h1 := (hρ 1).1
  have h2 := (hρ 2).1
  have h0' := (hρ 0).2
  have h1' := (hρ 1).2
  have h2' := (hρ 2).2
  generalize MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ 2
    = b at h ⊢
  fin_cases b
  · simp [StrategicPolicy.NonMonotone.c] at h
    linarith
  · simp [StrategicPolicy.NonMonotone.c] at h
    linarith
  · rfl

/-- Each scaled payoff `(q k - γ) * ρ k` lies in `[0, 9/10]`. -/
theorem term_bound (ρ : Fin 3 → ℝ) (hρ : ρ ∈ MonotoneBinary.Policies 3) (k : Fin 3) :
    0 ≤ (StrategicPolicy.NonMonotone.q k - StrategicPolicy.NonMonotone.γ) * ρ k ∧
      (StrategicPolicy.NonMonotone.q k - StrategicPolicy.NonMonotone.γ) * ρ k ≤ 9 / 10 := by
  have hk0 := (hρ k).1
  have hk1 := (hρ k).2
  fin_cases k
  · simp [StrategicPolicy.NonMonotone.q, StrategicPolicy.NonMonotone.γ] at hk0 hk1 ⊢
    constructor <;> nlinarith
  · simp [StrategicPolicy.NonMonotone.q, StrategicPolicy.NonMonotone.γ] at hk0 hk1 ⊢
    constructor <;> nlinarith
  · simp [StrategicPolicy.NonMonotone.q, StrategicPolicy.NonMonotone.γ] at hk0 hk1 ⊢
    constructor <;> nlinarith

/-- Expansion of the decision maker's utility. -/
theorem u_eq (ρ : Fin 3 → ℝ) :
    MonotoneBinary.u StrategicPolicy.NonMonotone.p StrategicPolicy.NonMonotone.q
        StrategicPolicy.NonMonotone.γ StrategicPolicy.NonMonotone.c ρ =
      1 / 10 * ((StrategicPolicy.NonMonotone.q
          (MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ 0) -
          StrategicPolicy.NonMonotone.γ) *
          ρ (MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ 0)) +
      2 / 5 * ((StrategicPolicy.NonMonotone.q
          (MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ 1) -
          StrategicPolicy.NonMonotone.γ) *
          ρ (MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ 1)) +
      1 / 2 * ((StrategicPolicy.NonMonotone.q
          (MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ 2) -
          StrategicPolicy.NonMonotone.γ) *
          ρ (MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ 2)) := by
  rw [MonotoneBinary.u, Fin.sum_univ_three]
  have e0 : StrategicPolicy.NonMonotone.p 0 = 1 / 10 := by simp [StrategicPolicy.NonMonotone.p]
  have e1 : StrategicPolicy.NonMonotone.p 1 = 2 / 5 := by simp [StrategicPolicy.NonMonotone.p]
  have e2 : StrategicPolicy.NonMonotone.p 2 = 1 / 2 := by simp [StrategicPolicy.NonMonotone.p]
  rw [e0, e1, e2]
  ring

/-- (L2) Upper bound on the utility of any policy. -/
theorem u_le (ρ : Fin 3 → ℝ) (hρ : ρ ∈ MonotoneBinary.Policies 3) :
    MonotoneBinary.u StrategicPolicy.NonMonotone.p StrategicPolicy.NonMonotone.q
        StrategicPolicy.NonMonotone.γ StrategicPolicy.NonMonotone.c ρ ≤ 6 / 10 := by
  rw [u_eq, br_two ρ hρ]
  have t0 := (term_bound ρ hρ
    (MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ 0)).2
  have t1 := (term_bound ρ hρ
    (MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q ρ 1)).2
  have hq2 : StrategicPolicy.NonMonotone.q 2 - StrategicPolicy.NonMonotone.γ = 3 / 10 := by
    simp [StrategicPolicy.NonMonotone.q, StrategicPolicy.NonMonotone.γ]
    norm_num
  rw [hq2]
  have h2 := (hρ 2).2
  linarith

/-- The witness policy. -/
noncomputable def π₀ : Fin 3 → ℝ := ![1, 0, 1]

theorem π₀_mem : π₀ ∈ MonotoneBinary.Policies 3 := by
  intro i
  fin_cases i <;> simp [π₀]

theorem π₀_br0 :
    MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q π₀ 0 = 0 := by
  apply br_eq_zero
  unfold MonotoneBinary.argmax
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro l
  fin_cases l <;> simp [π₀, StrategicPolicy.NonMonotone.c] <;> norm_num

theorem π₀_br1 :
    MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q π₀ 1 = 0 := by
  apply br_eq_zero
  unfold MonotoneBinary.argmax
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro l
  fin_cases l <;> simp [π₀, StrategicPolicy.NonMonotone.c] <;> norm_num

/-- (L3) The witness attains the upper bound `6/10`. -/
theorem u_π₀ :
    MonotoneBinary.u StrategicPolicy.NonMonotone.p StrategicPolicy.NonMonotone.q
        StrategicPolicy.NonMonotone.γ StrategicPolicy.NonMonotone.c π₀ = 6 / 10 := by
  rw [u_eq, π₀_br0, π₀_br1, br_two π₀ π₀_mem]
  simp [π₀, StrategicPolicy.NonMonotone.q, StrategicPolicy.NonMonotone.γ]
  norm_num

theorem π₀_isMaxOn :
    IsMaxOn (MonotoneBinary.u StrategicPolicy.NonMonotone.p StrategicPolicy.NonMonotone.q
        StrategicPolicy.NonMonotone.γ StrategicPolicy.NonMonotone.c)
      (MonotoneBinary.Policies 3) π₀ := by
  rw [isMaxOn_iff]
  intro ρ hρ
  rw [u_π₀]
  exact u_le ρ hρ

/-- Exclusion: no optimal policy is outcome monotonic. -/
theorem not_om (π : Fin 3 → ℝ) (hπ : π ∈ MonotoneBinary.Policies 3)
    (hmax : IsMaxOn (MonotoneBinary.u StrategicPolicy.NonMonotone.p StrategicPolicy.NonMonotone.q
        StrategicPolicy.NonMonotone.γ StrategicPolicy.NonMonotone.c)
      (MonotoneBinary.Policies 3) π) :
    ¬ MonotoneBinary.OMPolicy StrategicPolicy.NonMonotone.q π := by
  intro hom
  have hge := (isMaxOn_iff.mp hmax) π₀ π₀_mem
  rw [u_π₀, u_eq, br_two π hπ] at hge
  have t0 := (term_bound π hπ
    (MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q π 0)).2
  have t1 := (term_bound π hπ
    (MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q π 1)).2
  have hq2 : StrategicPolicy.NonMonotone.q 2 - StrategicPolicy.NonMonotone.γ = 3 / 10 := by
    simp [StrategicPolicy.NonMonotone.q, StrategicPolicy.NonMonotone.γ]
    norm_num
  rw [hq2] at hge
  have h0' := (hπ 0).2
  have h1' := (hπ 1).2
  have h1 := (hπ 1).1
  have h2' := (hπ 2).2
  have h2 := (hπ 2).1
  have hπ2 : 1 ≤ π 2 := by linarith
  have hT1 : 9 / 10 ≤ (StrategicPolicy.NonMonotone.q
      (MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q π 1) -
      StrategicPolicy.NonMonotone.γ) *
      π (MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q π 1) := by
    linarith
  have harg := br_argmax π 1 1
  generalize MonotoneBinary.br StrategicPolicy.NonMonotone.c StrategicPolicy.NonMonotone.q π 1
    = b at hT1 harg
  fin_cases b
  · simp [StrategicPolicy.NonMonotone.c] at harg
    have hlt : π 1 < π 2 := by linarith
    have hq := hom 1 2 hlt
    simp [StrategicPolicy.NonMonotone.q] at hq
    norm_num at hq
  · simp [StrategicPolicy.NonMonotone.q, StrategicPolicy.NonMonotone.γ] at hT1
    nlinarith
  · simp [StrategicPolicy.NonMonotone.q, StrategicPolicy.NonMonotone.γ] at hT1
    nlinarith

end StrategicPolicy.NonMonotone.Sol_StrategicPolicy_NonMonotone_no_outcome_monotonic_optimum

open StrategicPolicy.NonMonotone in
theorem solution :
    (∃ π : Fin 3 → ℝ, π ∈ StrategicPolicy.MonotoneBinary.Policies 3 ∧
      IsMaxOn (StrategicPolicy.MonotoneBinary.u StrategicPolicy.NonMonotone.p
        StrategicPolicy.NonMonotone.q StrategicPolicy.NonMonotone.γ StrategicPolicy.NonMonotone.c)
        (StrategicPolicy.MonotoneBinary.Policies 3) π) ∧
    (∀ π : Fin 3 → ℝ, π ∈ StrategicPolicy.MonotoneBinary.Policies 3 →
      IsMaxOn (StrategicPolicy.MonotoneBinary.u StrategicPolicy.NonMonotone.p
        StrategicPolicy.NonMonotone.q StrategicPolicy.NonMonotone.γ StrategicPolicy.NonMonotone.c)
        (StrategicPolicy.MonotoneBinary.Policies 3) π →
      ¬ StrategicPolicy.MonotoneBinary.OMPolicy StrategicPolicy.NonMonotone.q π) := by
  refine ⟨⟨Sol_StrategicPolicy_NonMonotone_no_outcome_monotonic_optimum.π₀,
    Sol_StrategicPolicy_NonMonotone_no_outcome_monotonic_optimum.π₀_mem,
    Sol_StrategicPolicy_NonMonotone_no_outcome_monotonic_optimum.π₀_isMaxOn⟩, ?_⟩
  · intro π hπ hmax
    exact Sol_StrategicPolicy_NonMonotone_no_outcome_monotonic_optimum.not_om π hπ hmax
