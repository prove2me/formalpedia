-- Prove2me | solution 1 for WilliamsonShmoys.maximality_edge_lower_bound__p2m_f7f91e8c_5069_473d_a1c5_2fecc5af85f8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:30:54.810454+00:00
-- url     : https://prove2.me/submissions/d9f4678f-c2dd-4576-921f-bcbcb4eea9b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_caf31ad8_7627_4591_a986_7fd32a9eba8e_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → HasPlanarDrawingOn N → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel M.Adj := dM;
      3 * Fintype.card V - 6 ≤ M.edgeFinset.card) := by
  classical
  obtain ⟨N, dN, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_caf31ad8_7627_4591_a986_7fd32a9eba8e_a1
      M hM hcard
  have hEq : N = M := hmax N hMN hN
  subst N
  have hd : dN = dM := Subsingleton.elim _ _
  subst dN
  omega