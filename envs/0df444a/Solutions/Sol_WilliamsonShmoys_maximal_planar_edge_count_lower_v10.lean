-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_v10
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:13:22.224013+00:00
-- url     : https://prove2.me/submissions/4ae07fe4-65be-4f9e-a46c-4bd03b4d3f68

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count_v2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N <= M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_edge_count_v2 M hV hM
  have hNM : N <= M := hmax N hMN hN
  have hEq : M = N := le_antisymm hMN hNM
  rw [hEq]
  omega