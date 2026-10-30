-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:17:16.851152+00:00
-- url     : https://prove2.me/submissions/1bd35196-d15c-4135-aa41-9bcaa001333b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_triangulated_extension_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_on_triangulated_extension_edge_count K hK hV
  have hLK : L ≤ K := hmax L hKL hL
  have hEq : K = L := le_antisymm hKL hLK
  rw [hEq]
  exact hcount