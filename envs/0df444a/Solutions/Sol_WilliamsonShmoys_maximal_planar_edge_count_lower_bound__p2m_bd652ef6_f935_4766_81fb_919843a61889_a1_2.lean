-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_bd652ef6_f935_4766_81fb_919843a61889_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:57:47.430726+00:00
-- url     : https://prove2.me/submissions/31aa503b-6813-490b-a9bd-accad07b065b

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count_20f2cea7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) (hV : 3 ≤ Fintype.card V) (hYmax : ∀ Z : SimpleGraph V, Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y) : 3 * Fintype.card V ≤ Y.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_drawable_supergraph_edge_count_20f2cea7 Y hY hV hYmax
