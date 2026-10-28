-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_drawing_edge_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:55:53.459988+00:00
-- url     : https://prove2.me/submissions/ca9d4eb9-cc83-49bd-90b5-36bb9d79a40b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_preserves_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hbound⟩ :=
    WilliamsonShmoys.planar_augmentation_preserves_lower_bound (K := K) hV hK
  have hcount := hmax L hKL hL
  exact hbound.trans (Nat.add_le_add_right hcount 6)