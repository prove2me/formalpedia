-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_via_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:51:47.345018+00:00
-- url     : https://prove2.me/submissions/728ec2b7-227a-4788-93c2-bf09e37e4f69
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_exact_edge_count_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    3 * Fintype.card V - 6 ≤ T.edgeSet.ncard := by
  obtain ⟨U, hTU, hU, hcount⟩ :=
    WilliamsonShmoys.planar_graph_has_exact_edge_count_supergraph T hV hT
  have hUT : U = T := hmax U hTU hU
  rw [hUT] at hcount
  omega