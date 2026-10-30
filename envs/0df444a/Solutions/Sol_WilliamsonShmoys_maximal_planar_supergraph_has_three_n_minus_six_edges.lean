-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_has_three_n_minus_six_edges
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:16:42.811564+00:00
-- url     : https://prove2.me/submissions/aed96862-8f5e-4913-b682-fa4a38154e43

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hcard⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulation_extension K hK hV
  have hEq : K = L := (hmax L hKL hL).symm
  rw [hEq]
  exact hcard