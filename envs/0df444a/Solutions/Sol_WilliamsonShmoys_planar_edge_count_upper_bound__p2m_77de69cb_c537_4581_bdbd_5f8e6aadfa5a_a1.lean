-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_77de69cb_c537_4581_bdbd_5f8e6aadfa5a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:02:12.032982+00:00
-- url     : https://prove2.me/submissions/2507b0e0-ad9c-4176-963f-30c95d2a08f6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_431d6cae_721e_4236_9ce2_a67c3b956bcb_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_431d6cae_721e_4236_9ce2_a67c3b956bcb_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hsub, hH, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_431d6cae_721e_4236_9ce2_a67c3b956bcb_a1 G hV hG
  exact (Set.ncard_mono hsub).trans
    (WilliamsonShmoys.maximal_planar_edge_bound__p2m_431d6cae_721e_4236_9ce2_a67c3b956bcb_a1 H hV hH hmax)