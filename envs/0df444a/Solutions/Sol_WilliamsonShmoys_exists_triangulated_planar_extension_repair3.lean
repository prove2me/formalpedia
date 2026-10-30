-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_extension_repair3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:15:08.62955+00:00
-- url     : https://prove2.me/submissions/a2ebe338-6397-4b5d-865d-53946ffeb443

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_3109df4d_98fd_4102_824c_39bdc30faaca
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_3109df4d_98fd_4102_824c_39bdc30faaca

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hK, hHK, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_3109df4d_98fd_4102_824c_39bdc30faaca H hH
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count_3109df4d_98fd_4102_824c_39bdc30faaca K hK hMax hCard
  exact ⟨K, hK, hHK, hCount⟩