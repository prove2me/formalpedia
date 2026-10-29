-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_count_maximal_edge_lower
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:44:00.454823+00:00
-- url     : https://prove2.me/submissions/bf9e0fab-563d-47c9-ab5a-81f5fac5d075

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨L, hKL, hLplanar, hLedges⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_supergraph K hV hK
  have hLK : L = K := hmax L hKL hLplanar
  subst L
  rw [hLedges]