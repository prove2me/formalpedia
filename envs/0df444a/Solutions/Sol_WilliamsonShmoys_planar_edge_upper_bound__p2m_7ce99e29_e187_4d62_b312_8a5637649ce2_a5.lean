-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_7ce99e29_e187_4d62_b312_8a5637649ce2_a5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:12:11.095144+00:00
-- url     : https://prove2.me/submissions/02e18385-40cb-4ba1-aadb-61b4d04205c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_maximal_extension__p2m_46fe5fa5_fbe5_4667_8617_73807c0b1344_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_46fe5fa5_fbe5_4667_8617_73807c0b1344_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hHK, hcard, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.planar_graph_maximal_extension__p2m_46fe5fa5_fbe5_4667_8617_73807c0b1344_a2 H hplanar
  have hKbound :=
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_46fe5fa5_fbe5_4667_8617_73807c0b1344_a2 K hKplanar hKmax hV
  omega