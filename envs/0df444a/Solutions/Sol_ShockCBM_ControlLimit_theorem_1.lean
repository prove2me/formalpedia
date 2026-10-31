-- Prove2me | solution 1 for ShockCBM.ControlLimit.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:10:41.46403+00:00
-- url     : https://prove2.me/submissions/617e5316-cd5f-4450-9c74-f6c449f914f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting
import Theorems.Thm_ShockCBM_ControlLimit_rhs19_monotone_x
import Theorems.Thm_ShockCBM_ControlLimit_rhs19_antitone_t

open ShockCBM.ControlLimit

theorem solution (M : Model) (hM : M.Standing) :
    ∃ δ : ℕ → ℕ → ℕ,
      (∀ n t : ℕ, δ n t ≤ M.ξ) ∧
      (∀ n t x : ℕ, x < M.ξ → (M.ReplaceOptimal (x, n, t) ↔ δ n t ≤ x)) ∧
      (∀ n : ℕ, Monotone (fun t => δ n t)) := by
  classical
  -- replacement is optimal at x, extended by `true` at x = ξ
  let P : ℕ → ℕ → ℕ → Prop := fun n t x => M.ReplaceOptimal (x, n, t) ∨ M.ξ ≤ x
  have hex : ∀ n t, ∃ x, P n t x := fun n t => ⟨M.ξ, Or.inr le_rfl⟩
  -- upward closure in x
  have hup : ∀ n t x x', x ≤ x' → M.ReplaceOptimal (x, n, t) → M.ReplaceOptimal (x', n, t) := by
    intro n t x x' hxx h
    have := rhs19_monotone_x M hM x x' n t hxx
    unfold Model.ReplaceOptimal at *
    have hγ := hM.γ_pos
    nlinarith
  -- downward closure in t
  have hdown : ∀ n t t' x, t ≤ t' → M.ReplaceOptimal (x, n, t') → M.ReplaceOptimal (x, n, t) := by
    intro n t t' x htt h
    have := rhs19_antitone_t M hM x n t t' htt
    unfold Model.ReplaceOptimal at *
    have hγ := hM.γ_pos
    nlinarith
  refine ⟨fun n t => Nat.find (hex n t), ?_, ?_, ?_⟩
  · intro n t
    exact Nat.find_min' (hex n t) (Or.inr le_rfl)
  · intro n t x hx
    constructor
    · intro h
      exact Nat.find_min' (hex n t) (Or.inl h)
    · intro h
      change Nat.find (hex n t) ≤ x at h
      have hs := Nat.find_spec (hex n t)
      rcases hs with hs | hs
      · exact hup n t _ x h hs
      · omega
  · intro n t t' htt
    show Nat.find (hex n t) ≤ Nat.find (hex n t')
    apply Nat.find_min' (hex n t)
    rcases Nat.find_spec (hex n t') with hs | hs
    · exact Or.inl (hdown n t t' _ htt hs)
    · exact Or.inr hs
