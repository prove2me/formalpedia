-- Prove2me | solution 1 for RobustSPUA.theorem_7_projection
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:42:31.22219+00:00
-- url     : https://prove2.me/submissions/16c0b846-6779-400e-b9a3-ea03c9e01f9e

import Mathlib
import Definitions.Def_RobustSPUA_Model
import Definitions.Def_RobustSPUA_LP

open Finset

namespace Aux_RSPUA7

open RobustSPUA

noncomputable def X (x : ℕ → ℕ → ℝ) (τ : ℕ) : ℝ := ∑ σ ∈ Icc 1 τ, x τ σ

theorem slack_one (p : ℝ) (x : ℕ → ℕ → ℝ) : slackLP p x 1 = 1 := by
  simp [slackLP]

theorem slack_succ (p : ℝ) (x : ℕ → ℕ → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    slackLP p x (t + 1) = slackLP p x t - p * X x t := by
  unfold slackLP X
  rw [Finset.sum_Ico_succ_top ht]
  ring

theorem polD_eq (p : ℝ) (x y : ℕ → ℕ → ℝ) (t : ℕ) :
    polD p x y (t + 1) = ∑ σ ∈ Icc 1 t, (x t σ + y t σ) - p * X x t := by
  unfold polD X
  simp only [Nat.add_sub_cancel]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  ring

end Aux_RSPUA7

open RobustSPUA Aux_RSPUA7 in
theorem solution (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∀ (x : ℕ → ℕ → ℝ) (γ : ℝ), (∃ y, PprimeFeasible n p x y γ) ↔ LPFeasible n p x γ := by
  intro x γ
  constructor
  · rintro ⟨y, ⟨hnn, h11, hrec⟩, hγ⟩
    have hS : ∀ τ, 1 ≤ τ → τ ≤ n → ∑ σ ∈ Icc 1 τ, (x τ σ + y τ σ) ≤ slackLP p x τ := by
      intro τ hτ1
      induction τ, hτ1 using Nat.le_induction with
      | base =>
        intro _
        rw [slack_one]
        simpa using h11
      | succ τ hτ ih =>
        intro hτn
        have hpos : (0 : ℝ) < ((τ + 1 : ℕ) : ℝ) := by positivity
        have h1 : ∑ σ ∈ Icc 1 (τ + 1), (x (τ + 1) σ + y (τ + 1) σ) ≤
            ∑ _σ ∈ Icc 1 (τ + 1), (1 / ((τ + 1 : ℕ) : ℝ)) * polD p x y (τ + 1) := by
          apply Finset.sum_le_sum
          intro σ hσ
          exact hrec (τ + 1) (Finset.mem_Icc.mpr ⟨by omega, hτn⟩) σ hσ
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel] at h1
        have h2 : ((τ + 1 : ℕ) : ℝ) * ((1 / ((τ + 1 : ℕ) : ℝ)) * polD p x y (τ + 1)) =
            polD p x y (τ + 1) := by field_simp
        rw [h2, polD_eq] at h1
        rw [slack_succ p x τ hτ]
        have := ih (by omega)
        linarith
    refine ⟨fun t ht s hs => ⟨(hnn t ht s hs).1, ?_⟩, fun k hk => ?_⟩
    · rw [Finset.mem_Icc] at ht hs
      by_cases ht1 : t = 1
      · subst ht1
        have hs1 : s = 1 := by omega
        subst hs1
        rw [slack_one]
        have := (hnn 1 (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩) 1 (Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)).2
        simp
        linarith
      · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
        have hu : 1 ≤ u := by omega
        have hxy := hrec (u + 1) (Finset.mem_Icc.mpr ⟨by omega, ht.2⟩) s (Finset.mem_Icc.mpr hs)
        have hy := (hnn (u + 1) (Finset.mem_Icc.mpr ⟨by omega, ht.2⟩) s (Finset.mem_Icc.mpr hs)).2
        have hP : polD p x y (u + 1) ≤ slackLP p x (u + 1) := by
          rw [polD_eq, slack_succ p x u hu]
          have := hS u hu (by omega)
          linarith
        have hpos : (0 : ℝ) ≤ 1 / ((u + 1 : ℕ) : ℝ) := by positivity
        calc x (u + 1) s ≤ x (u + 1) s + y (u + 1) s := by linarith
          _ ≤ 1 / ((u + 1 : ℕ) : ℝ) * polD p x y (u + 1) := hxy
          _ ≤ 1 / ((u + 1 : ℕ) : ℝ) * slackLP p x (u + 1) := mul_le_mul_of_nonneg_left hP hpos
    · have := hγ k hk
      calc γ ≤ p * (∑ t ∈ Icc 1 n, ∑ s ∈ Icc 1 t, x t s * rankCoef n t s k) /
            (1 - (1 - p) ^ k) := this
        _ = p / (1 - (1 - p) ^ k) * ∑ t ∈ Icc 1 n, ∑ s ∈ Icc 1 t, x t s * rankCoef n t s k := by
          ring
  · rintro ⟨hLP, hγ⟩
    refine ⟨fun t s => (1 / (t : ℝ)) * slackLP p x t - x t s, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro t ht s hs
      obtain ⟨h1, h2⟩ := hLP t ht s hs
      exact ⟨h1, by linarith⟩
    · simp only [Nat.cast_one, div_one, one_mul, slack_one]
      linarith
    · intro t ht s hs
      rw [Finset.mem_Icc] at ht
      obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      have hu : 1 ≤ u := by omega
      have hpd : polD p x (fun t s => (1 / (t : ℝ)) * slackLP p x t - x t s) (u + 1) =
          slackLP p x (u + 1) := by
        rw [polD_eq, slack_succ p x u hu]
        have : ∑ σ ∈ Icc 1 u, (x u σ + ((1 / (u : ℝ)) * slackLP p x u - x u σ)) =
            slackLP p x u := by
          have e : ∀ σ ∈ Icc 1 u, x u σ + ((1 / (u : ℝ)) * slackLP p x u - x u σ) =
              (1 / (u : ℝ)) * slackLP p x u := fun σ _ => by ring
          rw [Finset.sum_congr rfl e, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
            Nat.add_sub_cancel]
          have hu0 : (u : ℝ) ≠ 0 := by positivity
          field_simp
        rw [this]
      rw [hpd]
      simp only
      linarith
    · intro k hk
      have := hγ k hk
      calc γ ≤ p / (1 - (1 - p) ^ k) * ∑ t ∈ Icc 1 n, ∑ s ∈ Icc 1 t, x t s * rankCoef n t s k :=
            this
        _ = p * (∑ t ∈ Icc 1 n, ∑ s ∈ Icc 1 t, x t s * rankCoef n t s k) /
            (1 - (1 - p) ^ k) := by ring
