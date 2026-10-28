-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_lt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:42:42.671857+00:00
-- url     : https://prove2.me/submissions/d6428303-c30a-48c6-96aa-b027f343e94d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K L : SimpleGraph V) (h : K < L) : Nat.card {e : Sym2 V // e ∈ K.edgeSet} < Nat.card {e : Sym2 V // e ∈ L.edgeSet} := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact Set.ncard_lt_ncard (SimpleGraph.edgeSet_ssubset_edgeSet.2 h) (Set.toFinite _)
