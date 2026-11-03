-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:15:04.193167+00:00
-- url     : https://prove2.me/submissions/7d8f8b4a-c371-4a0d-b247-3a3aa776992f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulating_supergraph__p2m_d82f089b_ad0e_432a_8486_b2fabea854db_a1
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_mono__p2m_d82f089b_ad0e_432a_8486_b2fabea854db_a2
import Mathlib
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card) <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hMH, hHdraw, hHcard⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulating_supergraph__p2m_d82f089b_ad0e_432a_8486_b2fabea854db_a1
      M hcard hM
  have hmono := WilliamsonShmoys.edgeFinset_card_mono__p2m_d82f089b_ad0e_432a_8486_b2fabea854db_a2 M H hMH
  rw [hHcard] at hmono
  exact hmono