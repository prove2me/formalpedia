-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_b69f5d0b_8d80_4770_82d5_e0533af83150_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:01:14.810946+00:00
-- url     : https://prove2.me/submissions/24071234-0860-43aa-b5e0-c45c39ae31f2

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_extension_edge_count

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) : ∃ J : SimpleGraph V, H <= J ∧ HasPlanarDrawingOn J ∧ J.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulated_extension_edge_count H hH hV
