-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_from_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:27:12.13699+00:00
-- url     : https://prove2.me/submissions/07c00c9a-cc1e-4a02-a9c2-d230eca67327

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_tight_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_with_tight_edge_count K hK hcard
  have hLK : L = K := hmax L hKL hL
  simpa [hLK] using hcount