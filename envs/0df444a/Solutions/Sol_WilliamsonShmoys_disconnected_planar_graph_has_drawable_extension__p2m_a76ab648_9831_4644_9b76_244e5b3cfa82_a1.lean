-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_graph_has_drawable_extension__p2m_a76ab648_9831_4644_9b76_244e5b3cfa82_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:26:36.265988+00:00
-- url     : https://prove2.me/submissions/62a1450f-3e28-423b-ad2a-e65256fe6f8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_drawable_vertices_separated__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a1
import Theorems.Thm_WilliamsonShmoys_planar_bridge_between_separated_vertices__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a1
import Theorems.Thm_WilliamsonShmoys_edgeSet_strict_of_added_adj__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hdis : ¬ K.Connected) :
    ∃ M : SimpleGraph V,
      K.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ¬ M.edgeSet ⊆ K.edgeSet := by
  obtain ⟨u, v, huv⟩ :=
    WilliamsonShmoys.disconnected_drawable_vertices_separated__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a1
      K hdis
  obtain ⟨M, hsub, hMuv, hM⟩ :=
    WilliamsonShmoys.planar_bridge_between_separated_vertices__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a1
      K hK huv
  refine ⟨M, hsub, hM, ?_⟩
  exact WilliamsonShmoys.edgeSet_strict_of_added_adj__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a2
    K M hsub hMuv huv