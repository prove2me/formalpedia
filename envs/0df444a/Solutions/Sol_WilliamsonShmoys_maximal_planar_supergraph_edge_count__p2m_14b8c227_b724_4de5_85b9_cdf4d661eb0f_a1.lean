-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_14b8c227_b724_4de5_85b9_cdf4d661eb0f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:36:53.299963+00:00
-- url     : https://prove2.me/submissions/46a9818d-98e2-4f11-93ca-0355bbdd38ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_WilliamsonShmoys_maximal_planar_supergraph_edge_count_upper__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a6
import Theorems.Thm_WilliamsonShmoys_WilliamsonShmoys_planar_graph_edge_extension__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a6

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hP : HasPlanarDrawingOn P)
    (hmax : forall Q : SimpleGraph V, P <= Q -> HasPlanarDrawingOn Q -> Q <= P) :
    (letI : DecidableRel P.Adj := Classical.decRel P.Adj;
      3 * Fintype.card V = P.edgeFinset.card + 6) := by
  classical
  letI : DecidableRel P.Adj := Classical.decRel P.Adj
  have hup := WilliamsonShmoys.WilliamsonShmoys_maximal_planar_supergraph_edge_count_upper__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a6 P hV hP
  have hlow : 3 * Fintype.card V <= P.edgeFinset.card + 6 := by
    by_contra hnot
    have hlt : P.edgeFinset.card + 6 < 3 * Fintype.card V := Nat.lt_of_not_ge hnot
    obtain ⟨Q, hPQ, hQnotle, hQplanar⟩ :=
      WilliamsonShmoys.WilliamsonShmoys_planar_graph_edge_extension__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a6 P hV hP hlt
    exact hQnotle (hmax Q hPQ hQplanar)
  omega