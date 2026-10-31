-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_edc88f1d_7cba_486d_81b0_878aedf6c669_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:15:45.706991+00:00
-- url     : https://prove2.me/submissions/0a458e85-a483-4837-996d-cb98afa5dfc6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulated_supergraph_edge_bound__p2m_0b3a5bc9_5212_4922_863b_b35f1f108c76_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  classical
  obtain ⟨K, hHK, hKPlanar, hKbound⟩ :=
    WilliamsonShmoys.planar_triangulated_supergraph_edge_bound__p2m_0b3a5bc9_5212_4922_863b_b35f1f108c76_a1
      H hH hCard
  have hKH : K ≤ H := hMax K hHK hKPlanar
  have hEq : H = K := le_antisymm hHK hKH
  simpa [hEq] using hKbound