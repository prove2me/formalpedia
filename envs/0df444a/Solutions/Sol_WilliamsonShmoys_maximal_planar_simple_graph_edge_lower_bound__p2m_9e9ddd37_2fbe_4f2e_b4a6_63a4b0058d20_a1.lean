-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_9e9ddd37_2fbe_4f2e_b4a6_63a4b0058d20_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:25:40.26121+00:00
-- url     : https://prove2.me/submissions/52a3624b-9e17-4461-bcc4-8eca35715b88

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_strict_edge_augmentation__p2m_97e2a771_8b9b_4035_b979_2c6a9ee02dac_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ H : SimpleGraph V, M ≤ H → HasPlanarDrawingOn H → H = M)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  by_contra h
  have hSparse : M.edgeSet.ncard + 6 < 3 * Fintype.card V :=
    Nat.lt_of_not_ge h
  obtain ⟨H, hSub, hNe, hH⟩ :=
    WilliamsonShmoys.planar_strict_edge_augmentation__p2m_97e2a771_8b9b_4035_b979_2c6a9ee02dac_a1
      M hM hCard hSparse
  have hEq : H = M := hMax H hSub hH
  exact hNe hEq