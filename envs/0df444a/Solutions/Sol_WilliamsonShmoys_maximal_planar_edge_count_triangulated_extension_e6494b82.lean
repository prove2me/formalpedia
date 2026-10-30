-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_triangulated_extension_e6494b82
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:56:08.359975+00:00
-- url     : https://prove2.me/submissions/a34cfb1c-8f5e-4e22-af2b-24bc9a5f94b3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists_c4011bda_e2a2_4391_a47d_b4ea4febecd9
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_c4011bda_e2a2_4391_a47d_b4ea4febecd9

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hMax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists_c4011bda_e2a2_4391_a47d_b4ea4febecd9 M hM
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition_c4011bda_e2a2_4391_a47d_b4ea4febecd9
      N hN hMax hCard
  have hCount : N.edgeSet.ncard + 6 = 3 * Fintype.card V := by omega
  exact ⟨N, hMN, hN, hCount⟩