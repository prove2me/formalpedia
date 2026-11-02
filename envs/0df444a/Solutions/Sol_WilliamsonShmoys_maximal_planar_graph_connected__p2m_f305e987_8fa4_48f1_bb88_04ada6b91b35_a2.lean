-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_graph_connected__p2m_f305e987_8fa4_48f1_bb88_04ada6b91b35_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:48:09.592777+00:00
-- url     : https://prove2.me/submissions/01fe2b7b-73a0-496d-bd6a-b3d814c10c0b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_strict_planar_extension__p2m_2260a117_6439_491e_b3cc_351c9a5eff37_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.Connected := by
  by_contra hConnected
  obtain ⟨K, hGK, hK, hKG⟩ :=
    WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension__p2m_2260a117_6439_491e_b3cc_351c9a5eff37_a1
      G hcard hG hConnected
  exact hKG (hmax K hGK hK)