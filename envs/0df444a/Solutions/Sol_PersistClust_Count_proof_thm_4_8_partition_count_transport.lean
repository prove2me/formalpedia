-- Prove2me | solution 1 for PersistClust.Count.proof_thm_4_8_partition_count_transport
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T12:07:00.977863+00:00
-- url     : https://prove2.me/submissions/70dad6ea-e367-4a1e-8b4a-f932c57ac6d7

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Theorems.Thm_PersistClust_Count_proof_thm_4_8_partition_count_transport_forward
import Theorems.Thm_PersistClust_Count_proof_thm_4_8_partition_count_transport_reverse

/-!
# Theorem 4.8 (counting part), transport child — reduction to two grandchildren

`proof_thm_4_8_partition_count_transport` states equality 2 of the counting part of Theorem 4.8
of Chazal–Guibas–Oudot–Skraba (RR-6968, pp. 22–23): under `(d₁, d₂)`-separation of the
superlevel diagram `D` and a multi-bijection `γ : Copies D ≃ Copies D'` satisfying
assertions (i)–(iv) at threshold/radius `c·δ`, the number of `D`-copies in the closed region
`Δ^S_d₂ ∩ Λ^E_d₂` (prominence at least `d₂`, birth above `d₂`) equals the number of `D'`-copies
in the window region `Δ^S_τ ∩ Λ^E_τ`, where `τ` ranges in the window
`d₁ + 2cδ < τ < d₂ − 3cδ`.

The paper's proof exhibits `γ` restricted to the `Sum.inl` copies as a bijection between the two
copy sets, which yields the equality of encardinalities. This reduction factors that argument
into two independent grandchildren, one per direction of the equality:

1. `proof_thm_4_8_partition_count_transport_forward` (forward inequality): the map
   `q ↦ γ (Sum.inl q)` is injective and sends every `D`-copy whose point lies in
   `Δ^S_d₂ ∩ Λ^E_d₂` to a `D'`-copy whose point lies in `Δ^S_τ ∩ Λ^E_τ` (regions III–V of the
   paper: assertions (i)/(iii) of Theorem 4.5 at threshold `c·δ` keep the image in the window via
   the slack `τ < d₂ − 3cδ`; the QSE case bootstraps to QNE through assertions (i)/(ii) to
   control the second coordinate). Injectivity of `γ` gives
   `#copies(D, Δ^S_d₂ ∩ Λ^E_d₂) ≤ #copies(D', Δ^S_τ ∩ Λ^E_τ)`.

2. `proof_thm_4_8_partition_count_transport_reverse` (reverse inequality): `γ.symm` pulls a
   `D'`-copy whose point lies in `Δ^S_τ ∩ Λ^E_τ` back to an off-diagonal `D`-copy whose point
   `p` satisfies `p.2 ≤ p.1 − (τ − 2cδ) ≤ p.1 − d₁` (assertions (i)/(ii)/(iv) with
   `Δ^S_τ`-membership and the window inequality `d₁ + 2cδ < τ`; a diagonal copy is excluded
   because its equal coordinates would force `τ ≤ 2cδ`). Hence the preimage point is not in
   `Δ^N_d₁`, and `(d₁, d₂)`-separation places it in `Δ^S_d₂ ∩ Λ^E_d₂`. Injectivity of
   `γ.symm` gives `#copies(D', Δ^S_τ ∩ Λ^E_τ) ≤ #copies(D, Δ^S_d₂ ∩ Λ^E_d₂)`.

Both grandchildren carry exactly the binder block of the parent statement, so each instantiates
it verbatim, and the two inequalities combine by `le_antisymm` into the stated equality of
encardinalities.
-/

open PersistClust.Count

theorem solution
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (hsep : IsSeparated D d₁ d₂)
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ) :
    {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D q.1 ∧ q.1 ∈ DeltaS d₂ ∩ LamE d₂}.encard
      = {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D' q.1 ∧ q.1 ∈ DeltaS τ ∩ LamE τ}.encard :=
  le_antisymm
    (proof_thm_4_8_partition_count_transport_forward D D' hD hD' c δ hc hδ γ hγ d₁ d₂ hd₁ hδc
      hsep τ hτ₁ hτ₂)
    (proof_thm_4_8_partition_count_transport_reverse D D' hD hD' c δ hc hδ γ hγ d₁ d₂ hd₁ hδc
      hsep τ hτ₁ hτ₂)
