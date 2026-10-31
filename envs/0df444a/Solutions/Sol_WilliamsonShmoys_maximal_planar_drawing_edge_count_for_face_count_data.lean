-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_for_face_count_data
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:44:32.598347+00:00
-- url     : https://prove2.me/submissions/83191b41-3d8b-4302-b025-b43e17c55898

import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_repair_d02dec5c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarFaceCountData

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.edge_count_of_maximal_planar_drawing_repair_d02dec5c K hK hV hMax
