-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:46:07.452142+00:00
-- url     : https://prove2.me/submissions/ddf570eb-6761-4445-a04f-1be4a95bcb5e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_for_edge_bound_5164bdb5_triangulation_extension
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_triangulation_extension
      K hV hK
  have hLK : L = K := hmax L hKL hL
  simpa [hLK] using hcount