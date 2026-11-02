-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_edge_count__p2m_0e129449_44b7_4ec4_9782_615c2e23c561_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:14:20.422476+00:00
-- url     : https://prove2.me/submissions/a8fa7c26-bdcd-4c20-be88-86fc216e512d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_extension__p2m_625bb0fc_e249_4e4e_ba10_71dd29d5fb91_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_625bb0fc_e249_4e4e_ba10_71dd29d5fb91_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, ∃ dN : DecidableRel N.Adj,
        M ≤ N ∧ HasPlanarDrawingOn N ∧
        (letI : DecidableRel N.Adj := dN;
          6 * Fintype.card V = 2 * N.edgeFinset.card + 12) := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_edge_maximal_extension__p2m_625bb0fc_e249_4e4e_ba10_71dd29d5fb91_a1
      M hM hcard
  let dN : DecidableRel N.Adj := Classical.decRel N.Adj
  refine ⟨N, dN, hMN, hN, ?_⟩
  letI : DecidableRel N.Adj := dN
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_625bb0fc_e249_4e4e_ba10_71dd29d5fb91_a1
    N dN hN hmax hcard