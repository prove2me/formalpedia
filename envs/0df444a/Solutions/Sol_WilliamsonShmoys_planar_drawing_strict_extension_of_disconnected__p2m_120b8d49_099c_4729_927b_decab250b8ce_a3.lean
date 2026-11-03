-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_strict_extension_of_disconnected__p2m_120b8d49_099c_4729_927b_decab250b8ce_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:39:34.190051+00:00
-- url     : https://prove2.me/submissions/82bbf778-1607-4213-9ad2-63f78ee3f762

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_exists__p2m_10f04ae6_54c9_4ed6_b5cd_b1cd1816504e_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V, H < K ∧ HasPlanarDrawingOn K := by
  obtain ⟨K, hHK, hKConnected, hKDrawing⟩ :=
    WilliamsonShmoys.planar_connected_supergraph_exists__p2m_10f04ae6_54c9_4ed6_b5cd_b1cd1816504e_a1
      H hH hcard
  refine ⟨K, ?_, hKDrawing⟩
  have hne : H ≠ K := by
    intro hEq
    subst K
    exact hDisconnected hKConnected
  exact lt_of_le_of_ne hHK hne