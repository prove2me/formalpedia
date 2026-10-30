-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_nonempty_connected__p2m_ea88c89d_48b3_414b_a3f4_04bcb156f9eb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:04:05.76157+00:00
-- url     : https://prove2.me/submissions/3f732db6-efe0-4608-b766-429576a5e920
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_drawable_extension__p2m_a76ab648_9831_4644_9b76_244e5b3cfa82_a1

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
    WilliamsonShmoys.disconnected_planar_graph_has_drawable_extension__p2m_a76ab648_9831_4644_9b76_244e5b3cfa82_a1
      K hK hdis
  exact hstrict (hmax M hKM hM)