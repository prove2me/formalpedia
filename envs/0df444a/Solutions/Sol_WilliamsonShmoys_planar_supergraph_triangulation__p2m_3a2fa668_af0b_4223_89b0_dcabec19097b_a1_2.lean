-- Prove2me | solution 2 for WilliamsonShmoys.planar_supergraph_triangulation__p2m_3a2fa668_af0b_4223_89b0_dcabec19097b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:18:23.693048+00:00
-- url     : https://prove2.me/submissions/7339f586-5248-4849-9bed-dfad08b39bc5

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_has_triangulated_supergraph G hG hCard