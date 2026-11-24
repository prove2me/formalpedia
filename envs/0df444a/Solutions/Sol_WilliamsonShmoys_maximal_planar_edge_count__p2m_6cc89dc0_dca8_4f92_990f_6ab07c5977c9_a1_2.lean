-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_6cc89dc0_dca8_4f92_990f_6ab07c5977c9_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:26.339358+00:00
-- url     : https://prove2.me/submissions/4ad822eb-d35c-4b45-b156-63eb4163df10

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

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : LE.le 3 (Fintype.card V))
    (hT : HasPlanarDrawingOn T)
    (hmax : forall T' : SimpleGraph V, LE.le T T' -> HasPlanarDrawingOn T' -> T' = T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hMax' : ∀ J : SimpleGraph _, T ≤ J → HasPlanarDrawingOn J → J ≤ T := by
    intro J hHJ hJ
    exact (hmax J hHJ hJ).le
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc T hV hT hMax'
  omega
