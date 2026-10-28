-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_eq_euler
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:22:11.089984+00:00
-- url     : https://prove2.me/submissions/e6cbfc29-9a33-4453-825e-2ac0718a227d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_fd4411d1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_eq_euler_fd4411d1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨H, hKH, hHdraw, hHmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_fd4411d1 K hK
  have hHK : H ≤ K := hmax H hKH hHdraw
  have hgraph : H = K := le_antisymm hHK hKH
  have hcount :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_eq_euler_fd4411d1 H hHdraw hcard hHmax
  simpa [hgraph] using hcount