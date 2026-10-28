-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:05:10.747989+00:00
-- url     : https://prove2.me/submissions/5c3d54e8-729f-4a17-8c0f-66cb8747090e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_components_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_of_component_edge_steps_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L)
    (hV : 0 < Fintype.card V) :
    ∃ H : SimpleGraph V, L ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.planar_drawing_connected_supergraph_of_component_edge_steps_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
    L hdraw hV
    (fun G hg hnc =>
      WilliamsonShmoys.planar_drawing_add_edge_between_components_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f G hg hnc)