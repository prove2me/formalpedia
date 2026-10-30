-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_23341804_e9bd_4849_9be7_9e709bd142a9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:37:50.774814+00:00
-- url     : https://prove2.me/submissions/3391c6b8-a2b0-4498-be84-fb0d72ab7e97

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hLplanar, hLcount⟩ :=
    WilliamsonShmoys.planar_augmentation_edge_count K hK hCard
  have hLK : L ≤ K := hMax L hKL hLplanar
  have hcount : L.edgeSet.ncard ≤ K.edgeSet.ncard :=
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hLK)
  omega