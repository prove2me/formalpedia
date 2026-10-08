-- Prove2me | solution 1 for QLLL.quantum_lll_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:50:30.836901+00:00
-- url     : https://prove2.me/submissions/9b091d8b-b699-4583-b5d9-f5dc983a25f4

import Definitions.Def_QLLL_LocalLemma_Basic
import Theorems.Thm_QLLL_Valuation_lll_symmetric
import Mathlib

section

open QLLL
open Finset
open Module
variable {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable [FiniteDimensional 𝕜 V] [Nontrivial V]

theorem solution {m : ℕ} {X : Fin m → Submodule 𝕜 V}
    {Γ : Fin m → Finset (Fin m)} {p : ℝ} {d : ℕ}
    (hΓ : (relDimValuation (𝕜 := 𝕜) (V := V)).IsDependencyGraph X Γ)
    (hd : ∀ i, (Γ i).card ≤ d) (hX : ∀ i, 1 - p ≤ relDim (X i))
    (hp : p * Real.exp 1 * (d + 1) ≤ 1) :
    0 < relDim (Finset.univ.inf X) :=
  Valuation.lll_symmetric _ hΓ hd hX hp

end
