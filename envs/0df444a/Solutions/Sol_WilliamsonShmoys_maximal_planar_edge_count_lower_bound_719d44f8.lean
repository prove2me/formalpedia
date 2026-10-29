-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_719d44f8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:11:45.551627+00:00
-- url     : https://prove2.me/submissions/1a22dc71-076d-46cb-a0e6-74f6d8029d65

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph_719d44f8
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count_719d44f8

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  obtain ⟨K, hHK, hK, hmaxK⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph_719d44f8 H hH
  have hcount := WilliamsonShmoys.maximal_planar_graph_exact_edge_count_719d44f8
    K hV hK hmaxK
  have hKH : K = H := hmax K hHK hK
  rw [hKH] at hcount
  omega