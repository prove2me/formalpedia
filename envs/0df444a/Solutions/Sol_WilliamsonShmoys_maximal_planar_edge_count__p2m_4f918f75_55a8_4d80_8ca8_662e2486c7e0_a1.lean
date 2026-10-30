-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_4f918f75_55a8_4d80_8ca8_662e2486c7e0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:21:37.633183+00:00
-- url     : https://prove2.me/submissions/f4e23f7e-f526-4309-adb3-f9c939f162db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_1112e69e_48a4_4643_92d8_b48cd86b06af_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_1112e69e_48a4_4643_92d8_b48cd86b06af_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (C : L.ConnectedComponent)
    (M : SimpleGraph C.supp)
    [Fintype C.supp]
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph C.supp, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hcard : 3 ≤ C.supp.ncard) :
    M.edgeSet.ncard + 6 = 3 * C.supp.ncard := by
  have hUpper : M.edgeSet.ncard + 6 ≤ 3 * C.supp.ncard :=
    WilliamsonShmoys.planar_edge_upper_bound__p2m_1112e69e_48a4_4643_92d8_b48cd86b06af_a2
      L C M hDraw hcard
  have hLower : 3 * C.supp.ncard ≤ M.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_1112e69e_48a4_4643_92d8_b48cd86b06af_a2
      L C M hDraw hMax hcard
  exact Nat.le_antisymm hUpper hLower