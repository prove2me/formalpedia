-- Prove2me | solution 1 for Plasticity.SeqSpace.exists_signed_permutation_eq
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T08:09:06.041989+00:00
-- url     : https://prove2.me/submissions/d33caffa-4d0d-4b93-b500-ee3a109b1cc2

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_CUB37
import Theorems.Thm_Plasticity_SeqSpace_le_c0_of_bijOn_ballIn

open Plasticity

/-- CUB37 without its target hypothesis `Y ≤ c0 Δ`, which the normal form forces. -/
theorem solution {Γ Δ : Type*} (X : Submodule ℝ (Linf Γ)) (Y : Submodule ℝ (Linf Δ))
    (hX0 : c00 Γ ≤ X) (hX1 : X ≤ c0 Γ) (hY0 : c00 Δ ≤ Y)
    (hmatch : X = c00 Γ ∨ RealizesSignPatterns Y)
    (F : Linf Γ → Linf Δ)
    (hbij : Set.BijOn F (ballIn X) (ballIn Y))
    (hlip : LipschitzOnWith 1 F (ballIn X)) :
    ∃ σ : Γ ≃ Δ, ∃ α : Γ → ℝ, (∀ n, α n = 1 ∨ α n = -1) ∧
      ∀ x ∈ ballIn X, ∀ n, F x (σ n) = α n * x n :=
  Plasticity.CUB37 X Y hX0 hX1 hY0
    (Plasticity.SeqSpace.le_c0_of_bijOn_ballIn X Y hX0 hX1 hY0 F hbij hlip) hmatch F hbij hlip
