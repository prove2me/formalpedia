-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:49:06.743207+00:00
-- url     : https://prove2.me/submissions/f8c0df6f-f014-4074-a668-c81e30bd7f6b

import Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_extension_ws

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ L :=
  WilliamsonShmoys.planar_drawing_finite_maximal_extension_ws K hK
