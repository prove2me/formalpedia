-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_45b06a26_f6d7_4266_b401_312835dd7478_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:29:46.903131+00:00
-- url     : https://prove2.me/submissions/8ab9c913-932f-43ae-a17b-6fc89fa2f2d9

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_card_b74a49f4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_edge_card_b74a49f4 K hK hV hMax
