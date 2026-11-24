-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_connected__p2m_8955ab15_7b83_4a31_a256_432a7dfdfb1c_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:50:51.904744+00:00
-- url     : https://prove2.me/submissions/3381f66b-eee4-43ec-87cd-d4a144b95752

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hU : WilliamsonShmoys.HasPlanarDrawingOn U) (hUmax : ∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = U) : U.Connected := by
  have hMax' : ∀ J : SimpleGraph _, U ≤ J → HasPlanarDrawingOn J → J ≤ U := by
    intro J hHJ hJ
    exact (hUmax J hHJ hJ).le
  exact WilliamsonShmoys.maximal_planar_drawingOn_connected U hU hMax' hV
