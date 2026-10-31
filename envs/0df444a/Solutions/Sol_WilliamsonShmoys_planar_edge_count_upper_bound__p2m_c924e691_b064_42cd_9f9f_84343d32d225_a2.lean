-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c924e691_b064_42cd_9f9f_84343d32d225_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:33:54.702885+00:00
-- url     : https://prove2.me/submissions/e276af04-f6ed-4ad3-bd85-425ca5adc468
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_9a318fe1_85ed_4677_94d2_01eeb5a6121d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9a318fe1_85ed_4677_94d2_01eeb5a6121d_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨M, hNM, hM, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9a318fe1_85ed_4677_94d2_01eeb5a6121d_a1 N hN
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_9a318fe1_85ed_4677_94d2_01eeb5a6121d_a1 M hM hV hMax
  have hmono : N.edgeSet.ncard ≤ M.edgeSet.ncard := Set.ncard_mono hNM
  omega