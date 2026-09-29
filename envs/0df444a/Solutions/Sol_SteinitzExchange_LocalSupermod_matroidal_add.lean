-- Prove2me | solution 1 for SteinitzExchange.LocalSupermod.matroidal_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T14:41:52.40218+00:00
-- url     : https://prove2.me/submissions/5d518101-73bf-487a-86ac-3d895c179964

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal

open SteinitzExchange.LocalSupermod

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (h₁ h₂ : (V → ℝ) → ℝ) (hh₁ : IsPosHomogeneous h₁) (hh₂ : IsPosHomogeneous h₂)
    (hm₁ : IsMatroidal h₁) (hm₂ : IsMatroidal h₂) :
    IsMatroidal (h₁ + h₂) := by
  classical
  rcases hm₁ with ⟨hph₁, hc₁₁, hc₂₁⟩
  rcases hm₂ with ⟨hph₂, hc₁₂, hc₂₂⟩
  refine ⟨?_, ?_, ?_⟩
  · intro c hc₀ p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hph₁ c hc₀ p, hph₂ c hc₀ p]
    ring
  · intro X Y
    have e1 := hc₁₁ X Y
    have e2 := hc₁₂ X Y
    -- (C1): add the two supermodular inequalities. The two sides carry the
    -- same four atoms, only grouped differently, so `linarith` closes the goal
    -- without depending on how the parser nests the additions.
    simp only [Pi.add_apply]
    linarith
  · intro p σ hanti₀
    have e1 := hc₂₁ p σ hanti₀
    have e2 := hc₂₂ p σ hanti₀
    -- (C2): split the greedy sum pointwise with `mul_add`, then rewrite each
    -- half with the (C2) hypothesis for `h₁` and for `h₂`.
    simp only [Pi.add_apply]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← e1, ← e2]
