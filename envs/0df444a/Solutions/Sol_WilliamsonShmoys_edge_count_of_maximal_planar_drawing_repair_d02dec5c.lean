-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing_repair_d02dec5c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:34:34.929012+00:00
-- url     : https://prove2.me/submissions/bcedcf08-890a-4b83-95be-a443c7f3dd8b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_nat_edge_count_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hKmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hLplanar, hLcount⟩ :=
    WilliamsonShmoys.planar_drawing_nat_edge_count_completion K hKplanar hV
  have hLK : L = K := hKmax L hKL hLplanar
  rw [hLK] at hLcount
  exact hLcount