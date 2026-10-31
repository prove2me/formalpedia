-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_bound__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T20:51:46.262586+00:00
-- url     : https://prove2.me/submissions/e4d0444c-05c1-48c4-ba73-dc661fc8b113

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 <= Fintype.card V) : K.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound K hK hV
