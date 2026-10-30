-- Prove2me | solution 1 for SluggishCapability.Myopic.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:46:10.615454+00:00
-- url     : https://prove2.me/submissions/4c47901a-a132-47fb-9fa3-ded53a1c6415

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting
import Theorems.Thm_SluggishCapability_Myopic_ext_marginal_stationary
import Theorems.Thm_SluggishCapability_Myopic_recurrent_class_stationary
import Theorems.Thm_SluggishCapability_Myopic_step_3
import Theorems.Thm_SluggishCapability_Myopic_two_state_feasible
import Theorems.Thm_SluggishCapability_Myopic_part_ii_recurrent

open MarkovMixing
open SluggishCapability.Myopic

theorem solution (μ : ℕ) (hμ : 1 ≤ μ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (ε < 1 / 2 →
      ∀ (S : Type) [Fintype S] [DecidableEq S] (P : Matrix S S ℝ) (f : S → ℕ),
        IsFeasibleProgram P f μ ε → ∀ M : ℕ, (∀ s, f s ≤ M) →
        ∀ x : Fin (M + 1) × S, IsRecurrentState (extKernel P f M) x →
          ∃ y : Fin (M + 1) × S, Reaches (extKernel P f M) x y ∧ (y.1 : ℕ) ≤ 2 * μ - 1) ∧
    (∃ β₀ : ℝ, 0 ≤ β₀ ∧ β₀ < 1 ∧ ∀ β : ℝ, β₀ < β → β < 1 →
      IsFeasibleProgram (twoStateP β) (twoStateF μ) μ ε ∧
      ∀ M : ℕ, 2 * μ ≤ M →
        (∀ x : Fin (M + 1) × Fin 2,
          IsRecurrentState (extKernel (twoStateP β) (twoStateF μ) M) x ↔
            (((x.1 : ℕ) = 2 * μ - 1 ∧ x.2 = 0) ∨ ((x.1 : ℕ) = 2 * μ ∧ x.2 = 1))) ∧
        (∃ ν : Fin (M + 1) × Fin 2 → ℝ,
          IsStationary (extKernel (twoStateP β) (twoStateF μ) M) ν) ∧
        ∀ ν : Fin (M + 1) × Fin 2 → ℝ,
          IsStationary (extKernel (twoStateP β) (twoStateF μ) M) ν →
          ∀ x : Fin (M + 1) × Fin 2,
            ((x.1 : ℕ) = 2 * μ → x.2 = 1 → ν x = 1 / (1 + β)) ∧
            ((x.1 : ℕ) = 2 * μ - 1 → x.2 = 0 → ν x = β / (1 + β))) := by
  refine ⟨?_, ?_⟩
  · intro hhalf S _ _ P f hfeas M hM x hx
    have hK := (ext_marginal_stationary P f M hfeas.1 hM).1
    obtain ⟨ν, hν, -, hsupp⟩ := recurrent_class_stationary (extKernel P f M) hK x hx
    obtain ⟨y, hy, hyle⟩ := step_3 μ hμ ε hε0 hε1 hhalf P f hfeas M hM ν hν
    exact ⟨y, hsupp y hy, hyle⟩
  · obtain ⟨hA, hB⟩ := two_state_feasible μ
    obtain ⟨β₀, hβ₀0, hβ₀1, hβ₀⟩ := hB ε hε0
    refine ⟨β₀, hβ₀0, hβ₀1, fun β hβ hβ1 => ?_⟩
    have hβ0 : 0 < β := lt_of_le_of_lt hβ₀0 hβ
    obtain ⟨h1, h2, h3, h4⟩ := hA β hβ0 hβ1.le
    refine ⟨⟨h1, h2, _, h3, ?_⟩, fun M hM => part_ii_recurrent μ hμ β hβ0 hβ1 M hM⟩
    rw [h4]; exact hβ₀ β hβ hβ1
