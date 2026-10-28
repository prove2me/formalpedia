-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_3b82d126
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:03:39.17745+00:00
-- url     : https://prove2.me/submissions/bd444170-9028-41f5-9eb4-c95637a52e6d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_edge_lower_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      (∀ ⦃u v⦄, K.Adj u v → M.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      (∀ ⦃u v⦄, M.Adj u v → K.Adj u v)) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨M, hKM, hM, hbound⟩ :=
    WilliamsonShmoys.planar_extension_edge_lower_bound K hK hV
  have hMK : ∀ ⦃u v⦄, M.Adj u v → K.Adj u v := hmax M hKM hM
  have hEq : M = K := by
    ext u v
    constructor
    · intro huv
      exact hMK huv
    · intro huv
      exact hKM huv
  rw [hEq] at hbound
  exact hbound