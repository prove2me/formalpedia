-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ac994e54_6c64_49c2_8ec9_d8877c55139c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T03:07:19.93793+00:00
-- url     : https://prove2.me/submissions/9c8e0ab3-2ca5-4a7f-9507-d0a32a8dbd9b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_triangulation__p2m_8a3bb09f_be34_4160_8a3f_717a48932654_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      (forall {u v}, K.Adj u v -> L.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_completion_triangulation__p2m_8a3bb09f_be34_4160_8a3f_717a48932654_a2
      K hV hK
  have hLK : L = K := hmax L hKL hL
  subst L
  nlinarith [hcount]