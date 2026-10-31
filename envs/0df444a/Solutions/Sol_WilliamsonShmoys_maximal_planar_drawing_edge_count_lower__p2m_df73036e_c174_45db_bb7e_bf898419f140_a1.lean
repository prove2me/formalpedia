-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_df73036e_c174_45db_bb7e_bf898419f140_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:03:30.262314+00:00
-- url     : https://prove2.me/submissions/943dfdeb-cbc8-4398-a335-14ad9fe8b832

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_ec87327c_94d1_4f33_a35a_c8476e7ad1f3_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKDraw, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_ec87327c_94d1_4f33_a35a_c8476e7ad1f3_a1
      H hDraw hCard
  have hEq : K = H := hMax K hHK hKDraw
  subst K
  exact le_of_eq hCount