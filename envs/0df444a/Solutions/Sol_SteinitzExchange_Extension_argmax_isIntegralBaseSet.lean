-- Prove2me | solution 1 for SteinitzExchange.Extension.argmax_isIntegralBaseSet
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:58:21.483525+00:00
-- url     : https://prove2.me/submissions/e9ab8555-facd-4c6b-aeac-d67679e98afa

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

namespace SteinitzExchange.Extension

theorem aux_amibs_mem_argmaxB {V : Type*} (B : Finset (V → ℤ)) (g : (V → ℤ) → ℝ)
    (x : V → ℤ) : x ∈ argmaxB B g ↔ x ∈ B ∧ ∀ y ∈ B, g y ≤ g x := by
  unfold argmaxB
  rw [Finset.mem_filter]

end SteinitzExchange.Extension

open SteinitzExchange.Extension

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) :
    IsIntegralBaseSet (argmaxB B ω) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hxB, hx⟩ := B.exists_max_image ω hB.1
    exact ⟨x, (aux_amibs_mem_argmaxB B ω x).2 ⟨hxB, hx⟩⟩
  · intro x hx y hy u hu
    rw [aux_amibs_mem_argmaxB] at hx hy
    obtain ⟨v, hv, hx', hy', hle⟩ := hω x hx.1 y hy.1 u hu
    refine ⟨v, hv, (aux_amibs_mem_argmaxB B ω _).2 ⟨hx', fun z hz => ?_⟩⟩
    have h1 := hy.2 _ hy'
    have h2 := hx.2 z hz
    linarith
