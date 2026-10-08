-- Prove2me | solution 1 for QLLL.iInf_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:50:47.911997+00:00
-- url     : https://prove2.me/submissions/1bcb79ea-3620-435b-99d3-192db6957534

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_LocalLemma_Infinite
import Theorems.Thm_QLLL_lll_iInf
import Mathlib

section

open QLLL
open Finset
variable {α : Type*} [CompleteLattice α] (R : Valuation α)
variable {ι : Type*} {X : ι → α} {Γ : ι → Finset ι} {y : ι → ℝ}

theorem solution (hΓ : IsDependencyGraphOn R X Γ)
    (hy₀ : ∀ i, 0 ≤ y i) (hy₁ : ∀ i, y i < 1)
    (hX : ∀ i, 1 - y i * ∏ j ∈ Γ i, (1 - y j) ≤ R (X i))
    (c : ℝ) (hc : ∀ S : Finset ι, c ≤ ∏ j ∈ S, (1 - y j)) (hcpos : 0 < c)
    (hcont : ∀ b : ℝ, (∀ S : Finset ι, b ≤ R (S.inf X)) → b ≤ R (⨅ i, X i)) :
    (⨅ i, X i) ≠ ⊥ := by
  intro hbot
  have h := lll_iInf R hΓ hy₀ hy₁ hX c hc hcont
  rw [hbot, R.map_bot'] at h
  linarith

end
