-- Prove2me | solution 1 for WilliamsonShmoys.strict_edge_count_of_strict_subgraph__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:30:04.490171+00:00
-- url     : https://prove2.me/submissions/36802182-ec02-4a48-80f3-b8ab99545b79

import Mathlib

theorem solution {V : Type} [Fintype V] (K L : SimpleGraph V) (hKL : K ≤ L) (hne : K ≠ L) :
    K.edgeSet.ncard < L.edgeSet.ncard := by
  apply Set.ncard_lt_ncard
  · exact SimpleGraph.edgeSet_ssubset_edgeSet.mpr (lt_of_le_of_ne hKL hne)
  · exact Set.toFinite _