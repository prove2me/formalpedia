-- Prove2me | solution 1 for QLLL.quantum_lll
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:48:13.755589+00:00
-- url     : https://prove2.me/submissions/b9ab2a34-e16f-49e9-901c-837961ad9a23

import Definitions.Def_QLLL_LocalLemma_Basic
import Theorems.Thm_QLLL_Valuation_lll
import Mathlib

section

open QLLL
open Finset
open Module
variable {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable [FiniteDimensional 𝕜 V] [Nontrivial V]

theorem solution {m : ℕ} {X : Fin m → Submodule 𝕜 V}
    {Γ : Fin m → Finset (Fin m)} {y : Fin m → ℝ}
    (hΓ : (relDimValuation (𝕜 := 𝕜) (V := V)).IsDependencyGraph X Γ)
    (hy₀ : ∀ i, 0 ≤ y i) (hy₁ : ∀ i, y i < 1)
    (hX : ∀ i, 1 - y i * ∏ j ∈ Γ i, (1 - y j) ≤ relDim (X i)) :
    ∏ i, (1 - y i) ≤ relDim (Finset.univ.inf X) :=
  Valuation.lll _ hΓ hy₀ hy₁ hX

end
