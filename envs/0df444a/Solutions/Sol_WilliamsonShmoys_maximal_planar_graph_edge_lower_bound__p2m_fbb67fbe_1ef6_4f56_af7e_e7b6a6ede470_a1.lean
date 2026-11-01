-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_fbb67fbe_1ef6_4f56_af7e_e7b6a6ede470_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:30:00.119302+00:00
-- url     : https://prove2.me/submissions/a30f2b8a-26bd-42a7-b74d-66c079cd3e89
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_extension_edge_count__p2m_cd754a9f_7b3b_4f66_b68b_c9f75eba4801_a1
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_eq_of_graph_eq__p2m_cd754a9f_7b3b_4f66_b68b_c9f75eba4801_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 ≤ M.edgeFinset.card := by
  classical
  obtain ⟨N, hMN, hN, dN, hbound⟩ :=
    WilliamsonShmoys.drawable_triangulation_extension_edge_count__p2m_cd754a9f_7b3b_4f66_b68b_c9f75eba4801_a1
      M dM hM hcard
  letI : DecidableRel N.Adj := dN
  have hEq : N = M := hmax N hMN hN
  have hcardEq :=
    WilliamsonShmoys.edgeFinset_card_eq_of_graph_eq__p2m_cd754a9f_7b3b_4f66_b68b_c9f75eba4801_a3
      N M dN dM hEq
  calc
    3 * Fintype.card V - 6 ≤ N.edgeFinset.card := hbound
    _ = M.edgeFinset.card := hcardEq