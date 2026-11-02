-- Prove2me | solution 2 for WilliamsonShmoys.connected_of_maximal_planar__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:47:53.365688+00:00
-- url     : https://prove2.me/submissions/200ca7a8-77f2-44ac-82fe-e1e557a41ee6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_extension_of_disconnected_planar_graph__p2m_60fad162_757e_4f59_b943_b70a80142f4b_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.Connected := by
  by_contra hdisc
  obtain ⟨N, hMN, hN, hneq⟩ :=
    WilliamsonShmoys.drawable_extension_of_disconnected_planar_graph__p2m_60fad162_757e_4f59_b943_b70a80142f4b_a2
      M hM hcard hdisc
  exact hneq (hMax N hMN hN)