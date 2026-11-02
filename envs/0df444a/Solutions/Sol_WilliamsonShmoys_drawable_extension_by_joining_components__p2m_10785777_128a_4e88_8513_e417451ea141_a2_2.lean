-- Prove2me | solution 2 for WilliamsonShmoys.drawable_extension_by_joining_components__p2m_10785777_128a_4e88_8513_e417451ea141_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:59:24.795202+00:00
-- url     : https://prove2.me/submissions/28c77dd4-92ab-4de6-b486-a56c6f2706bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_has_unreachable_pair__p2m_0dfd7289_30fc_4048_8084_2297688a9abc_a2
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_components__p2m_0dfd7289_30fc_4048_8084_2297688a9abc_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hdisc : ¬ M.Connected) :
    ∃ u v : V, ¬ M.Reachable u v ∧
      ∃ N : SimpleGraph V, M ≤ N ∧ N.Adj u v ∧
        HasPlanarDrawingOn N ∧ N ≠ M := by
  obtain ⟨u, v, huv⟩ :=
    WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_0dfd7289_30fc_4048_8084_2297688a9abc_a2
      M hcard hdisc
  obtain ⟨N, hMN, huvN, hplanarN, hneq⟩ :=
    WilliamsonShmoys.planar_add_edge_between_components__p2m_0dfd7289_30fc_4048_8084_2297688a9abc_a1
      M hM u v huv
  exact ⟨u, v, huv, N, hMN, huvN, hplanarN, hneq⟩