-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_e31b05a7_4e78_4789_8a19_ecdeedbcdfa7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:02:51.07342+00:00
-- url     : https://prove2.me/submissions/5f9c8d3e-d715-43ae-89ef-57821ac3cbfb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_certificate__p2m_2b02d0f4_e4a5_4246_8c79_3e972b456778_a2
import Theorems.Thm_WilliamsonShmoys_planar_face_count_arithmetic__p2m_2b02d0f4_e4a5_4246_8c79_3e972b456778_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall P : SimpleGraph V, N <= P ->
      WilliamsonShmoys.HasPlanarDrawingOn P -> P = N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    N.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  obtain ⟨F, hF, length, hIncidence, hEuler, _hFaces, hTriangular⟩ :=
    WilliamsonShmoys.maximal_planar_face_certificate__p2m_2b02d0f4_e4a5_4246_8c79_3e972b456778_a2
      N hN hcard hmax
  letI : Fintype F := hF
  exact WilliamsonShmoys.planar_face_count_arithmetic__p2m_2b02d0f4_e4a5_4246_8c79_3e972b456778_a2
    (F := F) (n := Fintype.card V) (e := N.edgeFinset.card) length
    hcard hEuler hIncidence hTriangular
