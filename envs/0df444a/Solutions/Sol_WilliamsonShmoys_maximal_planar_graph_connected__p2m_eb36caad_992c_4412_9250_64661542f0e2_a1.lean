-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_connected__p2m_eb36caad_992c_4412_9250_64661542f0e2_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:54:05.150724+00:00
-- url     : https://prove2.me/submissions/44f0ad33-a83d-497b-92fa-ba3f0aae6644
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_of_disconnected__p2m_008dc069_b8e6_4096_b412_eae96eda23f6_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K)
    (hCard : 3 ≤ Fintype.card V) :
    K.Connected := by
  by_contra hConn
  obtain ⟨L, hKL, hL, hNotLK⟩ :=
    WilliamsonShmoys.planar_augmentation_of_disconnected__p2m_008dc069_b8e6_4096_b412_eae96eda23f6_a1
      K hK hConn
  exact hNotLK (hMax L hKL hL)