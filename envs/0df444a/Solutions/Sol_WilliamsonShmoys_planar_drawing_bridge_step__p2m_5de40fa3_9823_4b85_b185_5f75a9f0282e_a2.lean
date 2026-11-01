-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_bridge_step__p2m_5de40fa3_9823_4b85_b185_5f75a9f0282e_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:28:45.570832+00:00
-- url     : https://prove2.me/submissions/14bbd643-ee40-4d45-b57b-8097a4135e54
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_no_cross_edge_implies_not_reachable__p2m_806ab279_09f1_47fe_9b7f_fe9caced9bd3_a1
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_unreachable_vertices__p2m_806ab279_09f1_47fe_9b7f_fe9caced9bd3_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (A : Set V) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hno : ∀ u ∈ A, ∀ v ∉ A, ¬ G.Adj u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∃ u v, u ∈ A ∧ v ∉ A ∧ H.Adj u v := by
  obtain ⟨u, hu⟩ := hA
  obtain ⟨v, hv⟩ := hAc
  have hdisj : ¬ G.Reachable u v :=
    WilliamsonShmoys.no_cross_edge_implies_not_reachable__p2m_806ab279_09f1_47fe_9b7f_fe9caced9bd3_a1
      G A hno u v hu hv
  obtain ⟨H, hle, hplanar, hadj⟩ :=
    WilliamsonShmoys.planar_add_edge_between_unreachable_vertices__p2m_806ab279_09f1_47fe_9b7f_fe9caced9bd3_a1
      G hG u v hdisj
  exact ⟨H, hle, hplanar, ⟨u, v, hu, hv, hadj⟩⟩