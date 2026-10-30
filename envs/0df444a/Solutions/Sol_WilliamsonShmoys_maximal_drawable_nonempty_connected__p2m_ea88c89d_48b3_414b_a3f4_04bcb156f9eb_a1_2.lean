-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_nonempty_connected__p2m_ea88c89d_48b3_414b_a3f4_04bcb156f9eb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:44:02.257521+00:00
-- url     : https://prove2.me/submissions/d5dbc277-ca13-44e5-8ce5-39e4a7e30fa3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_disconnected_nonempty_planar_graph_has_drawable_extension__p2m_a76ab648_9831_4644_9b76_244e5b3cfa82_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 1 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax :
      ∀ M : SimpleGraph V,
        K.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet ⊆ K.edgeSet) :
    K.Connected := by
  by_contra hdis
  obtain ⟨M, hKM, hM, hstrict⟩ :=
    WilliamsonShmoys.disconnected_nonempty_planar_graph_has_drawable_extension__p2m_a76ab648_9831_4644_9b76_244e5b3cfa82_a2
      K hV hK hdis
  exact hstrict (hmax M hKM hM)