-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:48:53.859885+00:00
-- url     : https://prove2.me/submissions/07a86b9c-7ce7-4fce-971c-bcafc37f186f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_maximal_edge_count__p2m_b8edd37c_13b1_49cd_ab2a_13ab8a4421f7_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hdrawing : HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K -> HasPlanarDrawingOn K -> K = H) :
    (letI : forall K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj;
      H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  letI : forall K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
  obtain ⟨K, hsub, hKdraw, hKcard⟩ :=
    WilliamsonShmoys.planar_supergraph_with_maximal_edge_count__p2m_b8edd37c_13b1_49cd_ab2a_13ab8a4421f7_a1
      H hcard hdrawing
  have hKH : K = H := hmax K hsub hKdraw
  cases hKH
  exact hKcard
