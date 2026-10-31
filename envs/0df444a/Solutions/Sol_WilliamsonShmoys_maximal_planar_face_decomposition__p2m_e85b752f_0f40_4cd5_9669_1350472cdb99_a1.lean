-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_e85b752f_0f40_4cd5_9669_1350472cdb99_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:02:10.270518+00:00
-- url     : https://prove2.me/submissions/77e600c8-fee5-4183-8ab1-85096a481695

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_7ce99e29_e187_4d62_b312_8a5637649ce2_a5
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_7ce99e29_e187_4d62_b312_8a5637649ce2_a5

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hV : 3 <= Fintype.card V) :
    Exists (fun f : Nat => Fintype.card V + f = H.edgeSet.ncard + 2 /\
      3 * f = 2 * H.edgeSet.ncard) := by
  have hup := WilliamsonShmoys.planar_edge_upper_bound__p2m_7ce99e29_e187_4d62_b312_8a5637649ce2_a5
    H hplanar hV
  have hlo := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7ce99e29_e187_4d62_b312_8a5637649ce2_a5
    H hplanar hmax hV
  have hm : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by omega
  refine ⟨2 * Fintype.card V - 4, ?_⟩
  constructor <;> omega