-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:50:04.688846+00:00
-- url     : https://prove2.me/submissions/b6e27ad1-2be5-4b7c-9c7c-19116d3849d9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_edge_count_704fa243

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_augmentation_edge_count_704fa243 K hK hCard
  have hLK : L = K := hmax L hKL hL
  rw [hLK] at hcount
  exact hcount