-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_bound_set
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:56:18.251991+00:00
-- url     : https://prove2.me/submissions/165eee9f-fe46-45e1-a2d4-44fb5253514c

import Definitions.Def_ResourceScheduling_Graph_RAMSafe

set_option autoImplicit false
open ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (B : ℕ) (s : RAMState V) (hs : RAMBound B s)
    (v : V) (a : ℕ) (ha : a ≤ B) : RAMBound B (s.set v a) := by
  refine ⟨?_, hs.2⟩
  intro j
  by_cases h : j = v
  · subst j; simpa [RAMState.set] using ha
  · simpa [RAMState.set, h] using hs.1 j

#print axioms solution
