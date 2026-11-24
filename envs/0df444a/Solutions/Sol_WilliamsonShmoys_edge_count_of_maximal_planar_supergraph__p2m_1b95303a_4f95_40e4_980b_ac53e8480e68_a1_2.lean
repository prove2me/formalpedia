-- Prove2me | solution 2 for WilliamsonShmoys.edge_count_of_maximal_planar_supergraph__p2m_1b95303a_4f95_40e4_980b_ac53e8480e68_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:44.912918+00:00
-- url     : https://prove2.me/submissions/ed37a2b9-84c9-456f-abcf-cd76b63f6e39

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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hK : HasPlanarDrawingOn K) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ (L : SimpleGraph V) [DecidableRel L.Adj], K ≤ L → HasPlanarDrawingOn L → L = K) : 3 * Fintype.card V = K.edgeFinset.card + 6 := by
  have hMax' : ∀ J : SimpleGraph _, K ≤ J → HasPlanarDrawingOn J → J ≤ K := by
    intro J hHJ hJ
    exact (@hmax J (Classical.decRel _) hHJ hJ).le
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc K hcard hK hMax'
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  omega
