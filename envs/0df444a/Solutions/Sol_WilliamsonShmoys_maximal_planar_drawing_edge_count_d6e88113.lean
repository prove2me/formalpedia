-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_d6e88113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:55:20.808356+00:00
-- url     : https://prove2.me/submissions/12511737-a7f9-4d47-b1be-a4f69be0c059
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_d6e88113

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn K) (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, HasPlanarDrawingOn L → K ≤ L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hLdraw, hKL, hLcount⟩ :=
    WilliamsonShmoys.planar_completion_edge_count_d6e88113 K hdraw hV
  have hLK : L ≤ K := hmax L hLdraw hKL
  have hEq : K = L := le_antisymm hKL hLK
  rw [hEq]
  exact hLcount