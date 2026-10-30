-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_disconnected_connected_completion__p2m_9c676d6c_6d6d_407a_ad73_9f103d372166_a5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:05.695505+00:00
-- url     : https://prove2.me/submissions/f5b8e117-af52-44d9-92d0-ca49c0c6c623
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
import Theorems.Thm_WilliamsonShmoys_connected_maximal_planar_supergraph__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
import Theorems.Thm_WilliamsonShmoys_connected_strictly_more_edges__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) (hdisc : ¬ K.Connected) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧ H.Connected ∧
      K.edgeSet.ncard < H.edgeSet.ncard := by
  obtain ⟨H, hKH, hHP, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
      K hK hV
  have hHC : H.Connected :=
    WilliamsonShmoys.connected_maximal_planar_supergraph__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
      H hHP hV hmax
  have hstrict :=
    WilliamsonShmoys.connected_strictly_more_edges__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
      K H hKH hdisc hHC
  exact ⟨H, hKH, hHP, hHC, hstrict⟩
