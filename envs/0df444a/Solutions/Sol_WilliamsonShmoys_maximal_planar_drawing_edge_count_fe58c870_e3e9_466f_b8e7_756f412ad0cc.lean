-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_fe58c870_e3e9_466f_b8e7_756f412ad0cc
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:39:03.825154+00:00
-- url     : https://prove2.me/submissions/3ca05a5d-5328-445d-b326-d52f9c03b972

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_planar_drawing_dense_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hdense⟩ :=
    WilliamsonShmoys.planar_drawing_dense_supergraph H hV hH
  have hKH : K = H := hmax K hHK hK
  rw [hKH] at hdense
  exact Nat.le_antisymm
    (WilliamsonShmoys.planar_drawing_edge_count_upper_bound H hV hH)
    hdense