-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planarDrawingOn_upper_bound__p2m_4f160dcf_31cc_41b6_9e73_2a2d16cdab21_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:02:33.576439+00:00
-- url     : https://prove2.me/submissions/c1fd823e-431d-4fef-ae7c-d58379f048e7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_maximalExtension__p2m_bc222e64_5fd0_4544_bad9_127a7d6f7d68_a2
import Theorems.Thm_WilliamsonShmoys_maximalPlanar_edge_card__p2m_bc222e64_5fd0_4544_bad9_127a7d6f7d68_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel H.Adj := dH; H.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  letI : DecidableRel H.Adj := dH
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planarDrawingOn_maximalExtension__p2m_bc222e64_5fd0_4544_bad9_127a7d6f7d68_a2 H hH
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hKcard :=
    WilliamsonShmoys.maximalPlanar_edge_card__p2m_bc222e64_5fd0_4544_bad9_127a7d6f7d68_a2 K hK hmax hn
  have hle : H.edgeFinset.card ≤ K.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hHK)
  exact hle.trans (le_of_eq hKcard)