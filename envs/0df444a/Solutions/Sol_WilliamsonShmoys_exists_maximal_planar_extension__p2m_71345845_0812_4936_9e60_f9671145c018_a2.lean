-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension__p2m_71345845_0812_4936_9e60_f9671145c018_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:52:38.723737+00:00
-- url     : https://prove2.me/submissions/1bf40ab5-e108-4b93-815c-ab1dd93dd364

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_extension_maximizing_edge_count__p2m_3721485b_3cdc_4a3e_9978_b518aa3e9dbd_a1
import Theorems.Thm_WilliamsonShmoys_eq_of_le_and_edge_card_bound__p2m_3721485b_3cdc_4a3e_9978_b518aa3e9dbd_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T := by
  obtain ⟨T, hLT, hT, hmax⟩ :=
    WilliamsonShmoys.exists_drawable_extension_maximizing_edge_count__p2m_3721485b_3cdc_4a3e_9978_b518aa3e9dbd_a1 L hL
  refine ⟨T, hLT, hT, ?_⟩
  intro U hTU hU
  apply WilliamsonShmoys.eq_of_le_and_edge_card_bound__p2m_3721485b_3cdc_4a3e_9978_b518aa3e9dbd_a1 T U hTU
  exact hmax U (le_trans hLT hTU) hU
