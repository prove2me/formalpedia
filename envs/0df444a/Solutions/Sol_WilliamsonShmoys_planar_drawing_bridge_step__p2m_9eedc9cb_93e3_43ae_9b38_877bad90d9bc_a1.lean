-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_bridge_step__p2m_9eedc9cb_93e3_43ae_9b38_877bad90d9bc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:43:38.79999+00:00
-- url     : https://prove2.me/submissions/c158a33d-f6cb-4b64-878b-28a897249519
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_exists_maximal_supergraph__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
import Theorems.Thm_WilliamsonShmoys_disconnected_connected_supergraph_strict__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ H.Connected) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      H.edgeFinset ⊂ K.edgeFinset ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  classical
  obtain ⟨K, hdecK, hHK, hKdraw, hKmax⟩ :=
    WilliamsonShmoys.planar_drawing_exists_maximal_supergraph__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
      H hH
  letI : DecidableRel K.Adj := hdecK
  have hKconn :=
    WilliamsonShmoys.maximal_planar_drawing_connected__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
      K hKdraw hcard hKmax
  have hstrict :=
    WilliamsonShmoys.disconnected_connected_supergraph_strict__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
      H K hHK hdisconnected hKconn
  exact ⟨K, inferInstance, hstrict, hKdraw⟩
