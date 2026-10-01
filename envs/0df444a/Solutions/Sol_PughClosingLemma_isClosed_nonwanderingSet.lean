-- Prove2me | solution 1 for PughClosingLemma.isClosed_nonwanderingSet
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:11:43.033288+00:00
-- url     : https://prove2.me/submissions/d00e4106-8a6b-4258-bae8-202cd5474456

import Definitions.Def_PughClosingLemma_nonwandering

open scoped Topology
open PughClosingLemma

theorem solution {X : Type*} [TopologicalSpace X] (f : X → X) :
    IsClosed (nonwanderingSet f) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx U hU
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  obtain ⟨y, hyV, hy⟩ := mem_closure_iff.mp hx V hV hxV
  exact hy U (Filter.mem_of_superset (hV.mem_nhds hyV) hVU)
