-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_triangulation_extension_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:27:59.905822+00:00
-- url     : https://prove2.me/submissions/8206159d-31b3-4318-9488-1834ba3964cf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_same_vertices_20261026
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_20261026

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v) ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hH, hKH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_same_vertices_20261026 K hconn hK
  exact ⟨H, hH, hKH,
    WilliamsonShmoys.edge_maximal_planar_edge_count_20261026 H hH hmax hV⟩