-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:33:11.091757+00:00
-- url     : https://prove2.me/submissions/cf7d1a5b-997f-4fad-a79d-0bfd5690d0f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulated_completion_exists

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hcard⟩ :=
    WilliamsonShmoys.planar_triangulated_completion_exists L hL hV
  have hML : M ≤ L := hmax M hLM hM
  have hEq : M = L := le_antisymm hML hLM
  have hcardL : L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    simpa [hEq] using hcard
  exact le_of_eq hcardL.symm