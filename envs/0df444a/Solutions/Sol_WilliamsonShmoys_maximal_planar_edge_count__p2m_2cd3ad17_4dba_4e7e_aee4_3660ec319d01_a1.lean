-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_2cd3ad17_4dba_4e7e_aee4_3660ec319d01_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:36:52.710977+00:00
-- url     : https://prove2.me/submissions/35890d95-af34-4d04-8081-0f5c81ce9547
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph__p2m_370789e7_3e84_4b0d_bc08_210e85f3516c_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_370789e7_3e84_4b0d_bc08_210e85f3516c_a1 L hL hV
  have hEq : M = L := hmax M hLM hM
  simpa [hEq] using hcount