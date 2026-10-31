-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_insertion_below_triangulation_bound__p2m_e2c996e1_3289_4869_babc_b3655d7efc93_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:51:50.471998+00:00
-- url     : https://prove2.me/submissions/c9ebe2b9-5ddf-46c9-9d70-a8f14b74ad3f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulated_supergraph__p2m_7a004575_a295_4f3c_8d74_3fb00efa8d41_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hSparse : H.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ K ≠ H := by
  obtain ⟨K, hHK, hK, hTri⟩ :=
    WilliamsonShmoys.planar_triangulated_supergraph__p2m_7a004575_a295_4f3c_8d74_3fb00efa8d41_a1
      H hH hV
  refine ⟨K, hHK, hK, ?_⟩
  intro hEq
  have hCard : H.edgeSet.ncard = K.edgeSet.ncard := by
    simp [hEq]
  have hImpossible : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    calc
      H.edgeSet.ncard + 6 = K.edgeSet.ncard + 6 := by rw [hCard]
      _ = 3 * Fintype.card V := hTri
  omega