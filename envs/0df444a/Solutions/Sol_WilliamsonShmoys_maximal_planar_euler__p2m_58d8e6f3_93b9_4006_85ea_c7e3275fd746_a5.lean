-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a5
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:41:10.097803+00:00
-- url     : https://prove2.me/submissions/3bf240ac-6015-43e1-86fd-c960be9423fe

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
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 := by
  have hMax' : ∀ J : SimpleGraph _, L ≤ J → HasPlanarDrawingOn J → J ≤ L := by
    intro J hHJ hJ
    exact (hMax J hHJ hJ).le
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc L hCard hL hMax'
  exact ⟨2 * Fintype.card V - 4, by omega⟩
