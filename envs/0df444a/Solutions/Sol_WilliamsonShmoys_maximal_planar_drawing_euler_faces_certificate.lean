-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_euler_faces_certificate
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:41:10.747825+00:00
-- url     : https://prove2.me/submissions/b74fdf02-9b40-4714-b1ae-9cc9223eb09f

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
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    ∃ f : ℕ,
      2 * L.edgeSet.ncard = 3 * f ∧
      Fintype.card V + f = L.edgeSet.ncard + 2 := by
  have hMax' : ∀ J : SimpleGraph _, L ≤ J → HasPlanarDrawingOn J → J ≤ L := by
    intro J hHJ hJ
    exact (hmax J hHJ hJ).le
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc L hV hL hMax'
  exact ⟨2 * Fintype.card V - 4, by omega, by omega⟩
