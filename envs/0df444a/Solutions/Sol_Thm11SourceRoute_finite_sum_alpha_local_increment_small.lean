-- Prove2me | solution 1 for Thm11SourceRoute.finite_sum_alpha_local_increment_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:49:02.786662+00:00
-- url     : https://prove2.me/submissions/9f27f59c-6687-4146-a1f0-881997543e41

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F002
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset BigOperators
open Set Topology

noncomputable section

section Thm11SourceRoute
open Thm11SourceRoute


/-- Continuous-at local alpha increment with half-radius endpoints. -/
private theorem source_alpha_half_radius_increment
    {α : ℝ → ℝ} {c quota : ℝ}
    (hc : ContinuousAt α c) (hquota : 0 < quota) :
    ∃ delta : ℝ, 0 < delta ∧
      α (c + delta / 2) - α (c - delta / 2) < quota := by
  rcases continuousAt_alpha_local_increment (hc) hquota with
    ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  have hleft : |(c - delta / 2) - c| < delta := by
    refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith
  have hright : |(c + delta / 2) - c| < delta := by
    refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith
  exact Hdelta (c - delta / 2) (c + delta / 2) hleft hright

/-- The cardinality-weighted quota is strictly below the budget. -/
private theorem source_card_quota_lt
    (S : Finset ℝ) {eps : ℝ} (heps : 0 < eps) :
    (S.card : ℝ) * (eps / ((S.card : ℝ) + 1)) < eps := by
  let quota : ℝ := eps / ((S.card : ℝ) + 1)
  have hden_pos : 0 < (S.card : ℝ) + 1 := by positivity
  have hquota : 0 < quota := div_pos heps hden_pos
  have hcard_lt : (S.card : ℝ) < (S.card : ℝ) + 1 := by linarith
  have hmul_lt :
      (S.card : ℝ) * quota < ((S.card : ℝ) + 1) * quota :=
    mul_lt_mul_of_pos_right hcard_lt hquota
  have hquota_eq : ((S.card : ℝ) + 1) * quota = eps := by
    dsimp [quota]
    field_simp [ne_of_gt hden_pos]
  linarith

theorem solution {α : ℝ → ℝ}
    (S : Finset ℝ)
    (hα : ∀ c : ℝ, c ∈ S → ContinuousAt α c)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ → ℝ,
      (∀ c : ℝ, c ∈ S → 0 < rho c) ∧
      (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) < eps := by
  let quota : ℝ := eps / ((S.card : ℝ) + 1)
  have hden_pos : 0 < (S.card : ℝ) + 1 := by positivity
  have hquota : 0 < quota := div_pos heps hden_pos
  have hsmall :
      ∀ c : ℝ, c ∈ S →
        ∃ delta : ℝ, 0 < delta ∧
          α (c + delta / 2) - α (c - delta / 2) < quota := by
    intro c hc
    exact source_alpha_half_radius_increment (hα c hc) hquota
  let rho : ℝ → ℝ := fun c =>
    if hc : c ∈ S then Classical.choose (hsmall c hc) / 2 else 1
  refine ⟨rho, ?_, ?_⟩
  · intro c hc
    dsimp [rho]
    rw [dif_pos hc]
    have hdelta_pos : 0 < Classical.choose (hsmall c hc) :=
      (Classical.choose_spec (hsmall c hc)).1
    linarith
  · have hterm :
        ∀ c : ℝ, c ∈ S →
          α (c + rho c) - α (c - rho c) < quota := by
      intro c hc
      dsimp [rho]
      rw [dif_pos hc]
      exact (Classical.choose_spec (hsmall c hc)).2
    have hsum_le :
        (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) ≤
          ∑ _c ∈ S, quota := by
      refine Finset.sum_le_sum ?_
      intro c hc
      exact le_of_lt (hterm c hc)
    have hconst :
        (∑ _c ∈ S, quota) = (S.card : ℝ) * quota := by
      simp
    have hcard_quota_lt : (S.card : ℝ) * quota < eps := by
      simpa [quota] using source_card_quota_lt S heps
    exact lt_of_le_of_lt hsum_le (by simpa [hconst] using hcard_quota_lt)
end Thm11SourceRoute
