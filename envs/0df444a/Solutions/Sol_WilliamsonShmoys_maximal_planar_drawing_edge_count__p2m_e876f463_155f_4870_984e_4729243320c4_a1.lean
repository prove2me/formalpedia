-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e876f463_155f_4870_984e_4729243320c4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:56:54.135178+00:00
-- url     : https://prove2.me/submissions/53daf72f-2d48-4cee-adde-f1acbe7f2aec

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_689940da_6233_467d_b487_080b0de38a3b_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall Q : SimpleGraph V,
      (forall {u v : V}, P.Adj u v -> Q.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn Q ->
      (forall {u v : V}, Q.Adj u v -> P.Adj u v)) :
    letI : DecidableRel P.Adj := Classical.decRel P.Adj
    3 * Fintype.card V = P.edgeFinset.card + 6 := by
  classical
  letI : DecidableRel P.Adj := Classical.decRel P.Adj
  obtain ⟨Q, hPQ, hQ, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_689940da_6233_467d_b487_080b0de38a3b_a1
      P hP hcard
  have hQP : ∀ {u v : V}, Q.Adj u v → P.Adj u v := hmax Q hPQ hQ
  have hAdj : Q.Adj = P.Adj := by
    funext u v
    exact propext ⟨hQP, hPQ⟩
  have hEq : Q = P := SimpleGraph.ext hAdj
  subst Q
  exact hcount
