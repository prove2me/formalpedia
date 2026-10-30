-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:26:51.759502+00:00
-- url     : https://prove2.me/submissions/cd09700a-2be6-42b7-9029-6e15d994f9e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_upper_bound__p2m_648e2563_4933_48d5_af68_a43e4e82ab0d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_648e2563_4933_48d5_af68_a43e4e82ab0d_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hKmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hu := WilliamsonShmoys.planar_graph_edge_upper_bound__p2m_648e2563_4933_48d5_af68_a43e4e82ab0d_a1 K hK hV
  have hl := WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_648e2563_4933_48d5_af68_a43e4e82ab0d_a1 K hK hKmax hV
  omega