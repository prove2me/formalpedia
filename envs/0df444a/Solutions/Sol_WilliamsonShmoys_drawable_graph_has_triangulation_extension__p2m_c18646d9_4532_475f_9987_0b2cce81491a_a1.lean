-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulation_extension__p2m_c18646d9_4532_475f_9987_0b2cce81491a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:22:43.177987+00:00
-- url     : https://prove2.me/submissions/96d89697-2f59-4a0b-83b3-249dcdea5ae7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_20afdcd4_5dba_470f_a57a_287711f6e0ce_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_20afdcd4_5dba_470f_a57a_287711f6e0ce_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    Exists fun M : SimpleGraph V =>
      WilliamsonShmoys.HasPlanarDrawingOn M /\ L <= M /\
        3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  apply Exists.elim
    (WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_20afdcd4_5dba_470f_a57a_287711f6e0ce_a2
      L hL)
  intro M hM
  exact Exists.intro M
    (And.intro hM.1
      (And.intro hM.2.1
        (WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_20afdcd4_5dba_470f_a57a_287711f6e0ce_a2
          M hM.1 hM.2.2 hCard)))