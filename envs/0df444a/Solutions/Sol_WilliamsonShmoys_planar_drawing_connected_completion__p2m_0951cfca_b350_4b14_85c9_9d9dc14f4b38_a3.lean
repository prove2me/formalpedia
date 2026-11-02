-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_completion__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:56:41.776455+00:00
-- url     : https://prove2.me/submissions/b268d80c-458e-46ec-9256-eb80b7ac2bdd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_finite_step_completion__p2m_3b9c1b25_36f2_49fb_9760_e5ee7be0caf4_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_local_edge_extension__p2m_3b9c1b25_36f2_49fb_9760_e5ee7be0caf4_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      J.edgeFinset ⊆ H.edgeFinset := by
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  apply WilliamsonShmoys.planar_finite_step_completion__p2m_3b9c1b25_36f2_49fb_9760_e5ee7be0caf4_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) J hJ
  intro G hG u v hsep
  exact WilliamsonShmoys.planar_drawing_local_edge_extension__p2m_3b9c1b25_36f2_49fb_9760_e5ee7be0caf4_a1 G hG u v hsep