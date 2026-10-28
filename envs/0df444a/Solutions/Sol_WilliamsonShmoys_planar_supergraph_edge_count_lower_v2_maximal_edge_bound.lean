-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count_lower_v2_maximal_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:50:07.047878+00:00
-- url     : https://prove2.me/submissions/38792bac-f4d1-43f0-9cf0-ca23fe57828d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_v2_planar_augmentation

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N ≤ M) :
    3 * (Fintype.card V : Int) - 6 <= (M.edgeSet.ncard : Int) := by
  obtain ⟨N, hN, hMN, hBound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_count_lower_v2_planar_augmentation
      M hM hCard
  have hNM : N ≤ M := hMax N hN hMN
  have hEq : M = N := le_antisymm hMN hNM
  simpa [hEq] using hBound