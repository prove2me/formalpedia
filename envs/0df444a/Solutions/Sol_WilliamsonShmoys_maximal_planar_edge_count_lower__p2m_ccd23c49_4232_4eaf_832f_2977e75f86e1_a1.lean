-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_ccd23c49_4232_4eaf_832f_2977e75f86e1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:55:49.141413+00:00
-- url     : https://prove2.me/submissions/d7aad155-7f05-4f4b-a286-b62ceb8484bb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count__p2m_82e54da5_16cf_4d16_b293_9f40ba57f2f4_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall N : SimpleGraph V,
      M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N ->
      N <= M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  cases WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_82e54da5_16cf_4d16_b293_9f40ba57f2f4_a3
      M hM hCard with
  | intro N hParts =>
    cases hParts with
    | intro hMN hParts =>
      cases hParts with
      | intro hN hCount =>
        have hNM : N <= M := hMax N hMN hN
        have hEq : M = N := le_antisymm hMN hNM
        rw [hEq]
        omega