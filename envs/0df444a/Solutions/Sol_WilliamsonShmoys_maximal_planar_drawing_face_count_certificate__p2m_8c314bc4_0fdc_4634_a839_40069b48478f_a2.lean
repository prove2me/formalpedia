-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_count_certificate__p2m_8c314bc4_0fdc_4634_a839_40069b48478f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:47:54.991535+00:00
-- url     : https://prove2.me/submissions/c564e17b-65a1-421b-b314-4bea3103e9c0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e876f463_155f_4870_984e_4729243320c4_a1
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
    Exists fun F : ℕ =>
      Fintype.card V + F = P.edgeFinset.card + 2 ∧
      3 * F = 2 * P.edgeFinset.card := by
  classical
  letI : DecidableRel P.Adj := Classical.decRel P.Adj
  have hE := WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e876f463_155f_4870_984e_4729243320c4_a1
    P hP hcard hmax
  refine ⟨2 * Fintype.card V - 4, ?_⟩
  omega