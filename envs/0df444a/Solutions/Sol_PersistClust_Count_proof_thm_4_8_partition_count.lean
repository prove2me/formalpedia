-- Prove2me | solution 1 for PersistClust.Count.proof_thm_4_8_partition_count
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T10:10:43.814794+00:00
-- url     : https://prove2.me/submissions/ead0932f-8241-40d8-8b95-99ab4a4ce34a

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Theorems.Thm_PersistClust_Count_proof_thm_4_8_partition_count_sep
import Theorems.Thm_PersistClust_Count_proof_thm_4_8_partition_count_transport

/-!
# Theorem 4.8 (counting part) — reduction to two children

The milestone `proof_thm_4_8_partition_count` states the counting part of Theorem 4.8 of
Chazal–Guibas–Oudot–Skraba (RR-6968, p. 22): under `(d₁, d₂)`-separation of `D` and a
multi-bijection `γ : Copies D ≃ Copies D'` satisfying assertions (i)–(iv) with threshold/radius
`c·δ`, the number of off-diagonal copies of `D'` in the region `Δ^S_τ ∩ Λ^E_τ` (the `τ`-window
`d₁ + 2cδ < τ < d₂ − 3cδ`) equals `prominentCount D d₂`, the number of peaks of prominence at
least `d₂`.

The proof is the exact chain of the paper (end of the proof of Theorem 4.8): the diagram `D` is
split by separation into `D₁` (low prominence) and `D₂` (prominence ≥ `d₂`, birth > `d₂`), the
multi-bijection `γ` maps `D₂` onto the part of `D'` lying in `Δ^S_τ ∩ Λ^E_τ` while `D₁` maps
into the disjoint complement `Δ^N_{d₁+2cδ} ∪ Λ^W_{d₁+2cδ}`, and both `D₂` and its image avoid
the diagonal. Hence the `τ`-window count of `D'` equals the multiplicity of `D₂`, which by
separation is exactly the number of peaks of `D` of prominence at least `d₂`.

This reduction factors into two published children:

1. `proof_thm_4_8_partition_count_sep` (equality 1, source-side set equality): by separation every
   `D`-point of the closed half-plane `Δ^S_d₂` lies in `Δ^S_d₂ ∩ Λ^E_d₂`, so
   `prominentCount D d₂` equals the encardinality of the `D`-copies in `Δ^S_d₂ ∩ Λ^E_d₂`.
   It is applied with `d₁ < d₂`, which follows from `hδc`, `hc`, `hδ`.

2. `proof_thm_4_8_partition_count_transport` (equality 2, transport): `γ` restricts to a
   bijection between the `D`-copies in `Δ^S_d₂ ∩ Λ^E_d₂` and the `D'`-copies in
   `Δ^S_τ ∩ Λ^E_τ`, so the two copy sets have equal encardinality.

Chaining: `prominentCount D d₂ = [child 1] = #copies(D, Δ^S_d₂ ∩ Λ^E_d₂) = [child 2]
= #copies(D', Δ^S_τ ∩ Λ^E_τ)`, which is the statement.
-/

open PersistClust.Count

theorem solution
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (hsep : IsSeparated D d₁ d₂)
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ) :
    {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D' q.1 ∧ q.1 ∈ DeltaS τ ∩ LamE τ}.encard
      = prominentCount D d₂ := by
  -- `d₁ < d₂` follows from `hδc` (`5cδ < d₂ − d₁`) and positivity of `c`, `δ`.
  have h6 : δ * (5 * c) < d₂ - d₁ :=
    (lt_div_iff₀ (show (0 : ℝ) < 5 * c by positivity)).mp hδc
  have hd12 : d₁ < d₂ := by
    have h0 : (0 : ℝ) < δ * (5 * c) := by positivity
    linarith
  -- Child 1: prominence count equals the multiplicity of `D` in `Δ^S_d₂ ∩ Λ^E_d₂`.
  have hA : prominentCount D d₂ =
      {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D q.1 ∧ q.1 ∈ DeltaS d₂ ∩ LamE d₂}.encard :=
    proof_thm_4_8_partition_count_sep D hD d₁ d₂ hd₁ hsep hd12
  -- Child 2: γ transports that copy set to the `D'` copies in `Δ^S_τ ∩ Λ^E_τ`.
  have hB : {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D q.1 ∧ q.1 ∈ DeltaS d₂ ∩ LamE d₂}.encard
      = {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D' q.1 ∧ q.1 ∈ DeltaS τ ∩ LamE τ}.encard :=
    proof_thm_4_8_partition_count_transport D D' hD hD' c δ hc hδ γ hγ d₁ d₂ hd₁ hδc hsep τ hτ₁ hτ₂
  exact (hA.trans hB).symm
