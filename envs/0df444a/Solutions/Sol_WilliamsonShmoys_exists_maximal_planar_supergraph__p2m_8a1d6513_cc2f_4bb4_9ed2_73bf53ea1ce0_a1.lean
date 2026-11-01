-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8a1d6513_cc2f_4bb4_9ed2_73bf53ea1ce0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:26:16.349652+00:00
-- url     : https://prove2.me/submissions/4ca8cb7c-adc6-4a32-8150-0a7399e29b2b

import Theorems.Thm_WilliamsonShmoys_exists_maximal_edge_superset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a2
import Theorems.Thm_WilliamsonShmoys_connected_of_edgeFinset_subset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ K : SimpleGraph V,
      H.edgeFinset ⊆ K.edgeFinset ∧
      HasPlanarDrawingOn K ∧
      K.Connected ∧
      ∀ G : SimpleGraph V, K.edgeFinset ⊆ G.edgeFinset →
        HasPlanarDrawingOn G → G = K := by
  classical
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_edge_superset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a2
      H HasPlanarDrawingOn hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.connected_of_edgeFinset_subset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a2
      H K hHK hconn,
    hmax⟩