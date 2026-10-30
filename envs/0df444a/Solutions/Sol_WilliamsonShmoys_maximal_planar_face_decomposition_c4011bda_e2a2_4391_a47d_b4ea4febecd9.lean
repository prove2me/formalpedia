-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:26:08.998117+00:00
-- url     : https://prove2.me/submissions/cce29932-68b4-4bf6-b506-e01cb229f6a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_c4011bda_e2a2_4391_a47d_b4ea4febecd9
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_c4011bda_e2a2_4391_a47d_b4ea4febecd9

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_c4011bda_e2a2_4391_a47d_b4ea4febecd9 L hL hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_c4011bda_e2a2_4391_a47d_b4ea4febecd9 L hL hMax hCard
  have hEdges : 3 * Fintype.card V = L.edgeSet.ncard + 6 := by omega
  refine ⟨2 * Fintype.card V - 4, ?_⟩
  constructor <;> omega