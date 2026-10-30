-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_1112e69e_48a4_4643_92d8_b48cd86b06af_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:47:35.740508+00:00
-- url     : https://prove2.me/submissions/452f1d79-85fa-45b1-8104-db889f22c92b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_9011127c_6876_47eb_ac9e_306fd8c6abcc_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_edge_count__p2m_9011127c_6876_47eb_ac9e_306fd8c6abcc_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (C : L.ConnectedComponent)
    (M : SimpleGraph C.supp)
    [Fintype C.supp]
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ C.supp.ncard) :
    M.edgeSet.ncard + 6 ≤ 3 * C.supp.ncard := by
  obtain ⟨N, hDrawN, hCardLe, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_9011127c_6876_47eb_ac9e_306fd8c6abcc_a1
      M hDraw
  have hcard' : 3 ≤ (Set.univ : Set C.supp).ncard := by
    simpa using hcard
  have hEuler :=
    WilliamsonShmoys.maximal_planar_euler_edge_count__p2m_9011127c_6876_47eb_ac9e_306fd8c6abcc_a2
      N hDrawN hcard' hMax
  have huniv : (Set.univ : Set C.supp).ncard = C.supp.ncard := by
    simp
  omega