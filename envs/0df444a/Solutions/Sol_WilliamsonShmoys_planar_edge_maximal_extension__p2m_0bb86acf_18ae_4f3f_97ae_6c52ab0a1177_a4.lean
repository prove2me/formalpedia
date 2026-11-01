-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_extension__p2m_0bb86acf_18ae_4f3f_97ae_6c52ab0a1177_a4
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:11:16.225205+00:00
-- url     : https://prove2.me/submissions/6be12e82-2e42-4444-a6d7-751367fde932

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_finite_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, L.edgeSet ⊆ H.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet :=
  WilliamsonShmoys.exists_maximal_planar_extension_finite_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c L hDraw
