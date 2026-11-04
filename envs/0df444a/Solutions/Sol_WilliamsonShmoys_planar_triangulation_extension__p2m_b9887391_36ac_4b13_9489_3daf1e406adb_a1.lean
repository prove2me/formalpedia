-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_b9887391_36ac_4b13_9489_3daf1e406adb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:03:50.461369+00:00
-- url     : https://prove2.me/submissions/a5a62fb0-61be-4d22-a3d3-e73a31db2975

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_6d98c2a3_7d62_42a8_a794_93d41b1b40ef_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6d98c2a3_7d62_42a8_a794_93d41b1b40ef_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : Fintype ↥K.edgeSet := Fintype.ofFinite _
       K.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨K, hNK, hK, hmax⟩ := WilliamsonShmoys.planar_maximal_extension__p2m_6d98c2a3_7d62_42a8_a794_93d41b1b40ef_a1 N hN
  have hcard := WilliamsonShmoys.maximal_planar_edge_count__p2m_6d98c2a3_7d62_42a8_a794_93d41b1b40ef_a1 K hK hmax hV
  exact ⟨K, hNK, hK, hcard⟩
