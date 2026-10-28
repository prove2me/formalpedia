-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_e8a894df
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:42:05.389038+00:00
-- url     : https://prove2.me/submissions/7accbd4a-4df9-4ff7-9d86-ac3a74956bdb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_triangulated_completion_e8a894df

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.maximal_drawable_triangulated_completion_e8a894df K hV hK
  have hLK : L = K := hmax L hKL hL
  rw [← hLK]
  exact hcount