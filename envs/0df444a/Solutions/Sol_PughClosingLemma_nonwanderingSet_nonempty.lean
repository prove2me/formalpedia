-- Prove2me | solution 1 for PughClosingLemma.nonwanderingSet_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:12:04.064148+00:00
-- url     : https://prove2.me/submissions/8f93b129-895c-4c0d-bb02-94d1729f7250

import Definitions.Def_PughClosingLemma_nonwandering

open scoped Topology
open PughClosingLemma Filter

theorem solution {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] (f : X → X) : (nonwanderingSet f).Nonempty := by
  obtain ⟨z⟩ := ‹Nonempty X›
  obtain ⟨x, hx⟩ := exists_clusterPt_of_compactSpace
    (Filter.map (fun n : ℕ => f^[n] z) atTop)
  refine ⟨x, fun U hU => ?_⟩
  have hf : ∃ᶠ n : ℕ in atTop, f^[n] z ∈ U := frequently_map.mp (hx.frequently hU)
  obtain ⟨i, _, hi⟩ := frequently_atTop.mp hf 0
  obtain ⟨j, hij, hj⟩ := frequently_atTop.mp hf (i + 1)
  refine ⟨j - i, by omega, f^[j] z, ⟨f^[i] z, hi, ?_⟩, hj⟩
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega : i ≤ j)]
