-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_1112e69e_48a4_4643_92d8_b48cd86b06af_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:35:38.708109+00:00
-- url     : https://prove2.me/submissions/3ebc48ab-b008-4512-b9ef-6495634bcc52
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_edge_bound__p2m_a3d46af7_d8d1_44e5_ae3d_980c06c923f9_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (C : L.ConnectedComponent)
    (M : SimpleGraph C.supp)
    [Fintype C.supp]
    (hDraw : HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph C.supp, M ≤ N →
      HasPlanarDrawingOn N → N = M)
    (hcard : 3 ≤ C.supp.ncard) :
    3 * C.supp.ncard ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨N, hle, hNDraw, hbound⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_edge_bound__p2m_a3d46af7_d8d1_44e5_ae3d_980c06c923f9_a1
      C.supp M hDraw hcard
  have hNM : N = M := hMax N hle hNDraw
  rw [hNM] at hbound
  exact hbound