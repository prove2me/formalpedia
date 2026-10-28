-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_simple_graph_edge_count_lower_bound_a564c908_f139_469a_b89f_75ea35d29efc
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:40:20.284018+00:00
-- url     : https://prove2.me/submissions/35aa2d9e-8477-447b-90df-dbc3390fe945
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_supergraph_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ M : SimpleGraph V, N <= M → WilliamsonShmoys.HasPlanarDrawingOn M → M <= N) :
    3 * (Fintype.card V : Int) - 6 <= (N.edgeSet.ncard : Int) := by
  obtain ⟨M, hNM, hM, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_edge_count N hV hN
  have hMN : M <= N := hmax M hNM hM
  have hEq : N = M := le_antisymm hNM hMN
  rw [hEq]
  omega