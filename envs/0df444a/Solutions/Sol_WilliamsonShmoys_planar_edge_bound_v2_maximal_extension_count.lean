-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_v2_maximal_extension_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:13:45.026426+00:00
-- url     : https://prove2.me/submissions/748c5f98-79ea-45d9-9627-bb34dc75c7bd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_to_maximal_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hLplan, hcard⟩ :=
    WilliamsonShmoys.planar_augmentation_to_maximal_edge_count K hV hK
  have hLK := hmax L hKL hLplan
  have heq : L = K := le_antisymm hLK hKL
  simpa [heq] using hcard
