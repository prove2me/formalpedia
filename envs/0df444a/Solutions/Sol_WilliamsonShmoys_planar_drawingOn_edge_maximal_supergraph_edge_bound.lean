-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_edge_maximal_supergraph_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:11:26.75518+00:00
-- url     : https://prove2.me/submissions/596c3c21-f1c8-4bfa-a3cb-98b785582992

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_count_e5a7f9d6
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → K ≤ L → L ≤ K) :
    3 * (Fintype.card V : Int) - 6 <= (K.edgeSet.ncard : Int) := by
  obtain ⟨L, hL, hKL, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_completion_edge_count_e5a7f9d6 K hK hCard
  have hLK : L ≤ K := hmax L hL hKL
  have hEq : K = L := le_antisymm hKL hLK
  rw [hEq]
  omega