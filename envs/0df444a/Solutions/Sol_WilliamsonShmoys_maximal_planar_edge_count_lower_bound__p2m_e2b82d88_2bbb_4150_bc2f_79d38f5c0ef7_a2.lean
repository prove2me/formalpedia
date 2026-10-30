-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e2b82d88_2bbb_4150_bc2f_79d38f5c0ef7_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:23:43.642519+00:00
-- url     : https://prove2.me/submissions/ca99fe3e-8a6d-4fae-9515-6b90676f6cff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_completion__p2m_3bdd09ac_e2e3_4767_b598_2a6e24b78964_a1
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by
  obtain ⟨K, hNK, hKPlanar, hEdges⟩ :=
    WilliamsonShmoys.maximal_planar_triangulation_completion__p2m_3bdd09ac_e2e3_4767_b598_2a6e24b78964_a1
      N hN hCard
  have hKN : K = N := hMax K hNK hKPlanar
  have hNEdges : N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    simpa [hKN] using hEdges
  omega