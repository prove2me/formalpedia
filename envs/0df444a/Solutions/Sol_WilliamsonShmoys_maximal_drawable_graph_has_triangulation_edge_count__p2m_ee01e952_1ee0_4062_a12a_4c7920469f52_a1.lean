-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count__p2m_ee01e952_1ee0_4062_a12a_4c7920469f52_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:55:46.293254+00:00
-- url     : https://prove2.me/submissions/7e54cbfb-f813-493f-9ba0-97293b8bad93

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_drawable_supergraph__p2m_afa4574a_1607_44bb_93bd_58940dcb1487_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [hMdec : DecidableRel M.Adj] (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V = M.edgeFinset.card + 6 := by
  obtain ⟨N, hNdec, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.exists_triangulated_drawable_supergraph__p2m_afa4574a_1607_44bb_93bd_58940dcb1487_a2
      M hcard hM
  letI : DecidableRel N.Adj := hNdec
  have hEq : N = M := hmax N hMN hN
  subst N
  have hdeceq : hNdec = hMdec := Subsingleton.elim _ _
  subst hNdec
  exact hcount.symm