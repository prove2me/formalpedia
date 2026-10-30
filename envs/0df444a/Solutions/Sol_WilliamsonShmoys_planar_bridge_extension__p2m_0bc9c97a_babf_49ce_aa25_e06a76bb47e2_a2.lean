-- Prove2me | solution 1 for WilliamsonShmoys.planar_bridge_extension__p2m_0bc9c97a_babf_49ce_aa25_e06a76bb47e2_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:19:51.867694+00:00
-- url     : https://prove2.me/submissions/bd60238b-6424-4cbf-91f5-0a62476d65d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge_edge__p2m_5b011f3a_cb0c_4217_84d6_286f15b556e3_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (u v : V) (huv : Not (u = v)) (hnotreach : Not (G.Reachable u v)) :
    Exists fun K : SimpleGraph V => And (LE.le G K)
      (And (Not (G = K)) (HasPlanarDrawingOn K)) := by
  obtain ⟨K, hAdj, hstrict, hK⟩ :=
    WilliamsonShmoys.planar_drawing_add_bridge_edge__p2m_5b011f3a_cb0c_4217_84d6_286f15b556e3_a4
      G hG u v huv hnotreach
  refine ⟨K, ?_, ?_, hK⟩
  · intro a b hab
    exact (hAdj a b).2 (Or.inl hab)
  · intro hGK
    exact hstrict hGK.symm