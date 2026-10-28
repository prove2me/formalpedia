-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_edge_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:22:10.266986+00:00
-- url     : https://prove2.me/submissions/41da7fbb-6614-450c-9e86-e67e443ba1ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_exists_for_edge_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_via_euler

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      (∀ ⦃u v⦄, K.Adj u v → M.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨M, hKM, hM, hmax⟩ :=
    WilliamsonShmoys.planar_extension_exists_for_edge_bound K hK
  refine ⟨M, hKM, hM, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_lower_bound_via_euler M hM hV hmax