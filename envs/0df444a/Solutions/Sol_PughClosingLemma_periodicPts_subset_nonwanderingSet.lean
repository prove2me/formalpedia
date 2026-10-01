-- Prove2me | solution 1 for PughClosingLemma.periodicPts_subset_nonwanderingSet
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:11:54.016366+00:00
-- url     : https://prove2.me/submissions/2315b0e6-4885-450a-9ce7-8d0d1c7b67c5

import Definitions.Def_PughClosingLemma_nonwandering

open scoped Topology
open PughClosingLemma

theorem solution {X : Type*} [TopologicalSpace X] (f : X → X) :
    Function.periodicPts f ⊆ nonwanderingSet f := by
  intro x hx U hU
  obtain ⟨n, hn, hnx⟩ := hx
  have hxU := mem_of_mem_nhds hU
  exact ⟨n, hn, x, ⟨x, hxU, hnx⟩, hxU⟩
