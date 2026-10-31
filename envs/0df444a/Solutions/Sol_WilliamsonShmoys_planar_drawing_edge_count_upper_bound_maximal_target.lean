-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound_maximal_target
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:15:52.295426+00:00
-- url     : https://prove2.me/submissions/f1dec7a8-2ea2-4770-a50e-69ef559cf77f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarFaceCountData
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_39491eab_3342_47a8_bf1b_b037fb68e8e4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count_data_39491eab_3342_47a8_bf1b_b037fb68e8e4
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_face_count_bound_39491eab_3342_47a8_bf1b_b037fb68e8e4
import Theorems.Thm_WilliamsonShmoys_subgraph_edge_count_bound_39491eab_3342_47a8_bf1b_b037fb68e8e4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_39491eab_3342_47a8_bf1b_b037fb68e8e4 H hH
  obtain ⟨d⟩ := WilliamsonShmoys.maximal_planar_drawing_face_count_data_39491eab_3342_47a8_bf1b_b037fb68e8e4
    K hK hV hMax
  have hKbound := WilliamsonShmoys.planar_triangulation_face_count_bound_39491eab_3342_47a8_bf1b_b037fb68e8e4 K d
  exact WilliamsonShmoys.subgraph_edge_count_bound_39491eab_3342_47a8_bf1b_b037fb68e8e4
    H K hHK (le_of_eq hKbound)