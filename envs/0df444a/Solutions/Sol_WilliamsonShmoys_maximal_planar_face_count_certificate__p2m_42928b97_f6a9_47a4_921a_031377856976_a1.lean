-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_count_certificate__p2m_42928b97_f6a9_47a4_921a_031377856976_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:03:38.293324+00:00
-- url     : https://prove2.me/submissions/c32d8094-045e-44ba-b909-8e67bdd60e30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_6a345071_3a17_4f5f_baeb_1c2d7606cf05_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6a345071_3a17_4f5f_baeb_1c2d7606cf05_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  obtain ⟨H, hKH, hH, hmaxH⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_6a345071_3a17_4f5f_baeb_1c2d7606cf05_a1
      K hK
  have hHK : H ≤ K := hmax H hKH hH
  have hEq : H = K := le_antisymm hHK hKH
  have hEdge :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_6a345071_3a17_4f5f_baeb_1c2d7606cf05_a1
      H hcard hH hmaxH
  have hEdgeK : K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    simpa [hEq] using hEdge
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega