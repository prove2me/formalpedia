-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_edge_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:20:09.717993+00:00
-- url     : https://prove2.me/submissions/070a5ad0-e501-48a4-915a-bd4934cd97d3

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_extension__p2m_9379b763_2dc6_43e2_b02a_b18a7334854d_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 ≤ Fintype.card V)
    (hsmall : X.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ Y : SimpleGraph V, X < Y ∧ WilliamsonShmoys.HasPlanarDrawingOn Y :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count_extension__p2m_9379b763_2dc6_43e2_b02a_b18a7334854d_a1 X hdraw hV hsmall
