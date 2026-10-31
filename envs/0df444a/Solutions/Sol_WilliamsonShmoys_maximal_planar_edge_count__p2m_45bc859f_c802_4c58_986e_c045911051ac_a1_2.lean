-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_45bc859f_c802_4c58_986e_c045911051ac_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:36:33.643544+00:00
-- url     : https://prove2.me/submissions/528bf6a1-5bc7-498f-811e-75cdcfb22553

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) (hMax : ∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) (hCard : 3 ≤ Fintype.card V) : J.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1 J hDraw hMax hCard
