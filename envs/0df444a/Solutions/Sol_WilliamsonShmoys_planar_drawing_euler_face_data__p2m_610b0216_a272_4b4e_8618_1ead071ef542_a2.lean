-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:30:57.858994+00:00
-- url     : https://prove2.me/submissions/5ed88d30-694a-4d12-87ab-f9c1687c0699
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_system__p2m_badb0730_b4d5_45ef_abd7_880e94965ba4_a1
import Theorems.Thm_WilliamsonShmoys_directed_adj_card_eq_twice_edgeSet_ncard__p2m_badb0730_b4d5_45ef_abd7_880e94965ba4_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hplanar : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (q : ℕ)
      (face : {e : V × V // H.Adj e.1 e.2} → Fin q),
      Fintype.card {e : V × V // H.Adj e.1 e.2} = 2 * H.edgeSet.ncard ∧
      Fintype.card V + q = H.edgeSet.ncard + 2 ∧
      ∀ f : Fin q,
        3 ≤ Fintype.card {d : {e : V × V // H.Adj e.1 e.2} // face d = f} := by
  obtain ⟨q, face, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_face_system__p2m_badb0730_b4d5_45ef_abd7_880e94965ba4_a1
      H hplanar hconn hV
  have hDarts :=
    WilliamsonShmoys.directed_adj_card_eq_twice_edgeSet_ncard__p2m_badb0730_b4d5_45ef_abd7_880e94965ba4_a1
      H
  exact ⟨q, face, hDarts, hEuler, hFaces⟩