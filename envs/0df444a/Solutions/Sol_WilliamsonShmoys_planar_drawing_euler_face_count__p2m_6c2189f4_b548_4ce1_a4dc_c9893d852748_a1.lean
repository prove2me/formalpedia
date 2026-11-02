-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count__p2m_6c2189f4_b548_4ce1_a4dc_c9893d852748_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:16:59.275318+00:00
-- url     : https://prove2.me/submissions/58b559b4-fdb4-43ee-bce8-39f862abeca2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_count_certificate__p2m_0a6cb8c8_85f4_4527_b550_0c59830e1a8e_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hcard : 3 <= Fintype.card V) :
    Exists fun f : Nat => And (Fintype.card V + f = M.edgeFinset.card + 2)
      (3 * f <= 2 * M.edgeFinset.card) := by
  letI : DecidableRel M.Adj := dM
  have hedge : M.edgeSet.ncard = M.edgeFinset.card := by
    classical
    have hfinite : M.edgeSet.Finite := Set.finite_univ.subset (Set.subset_univ _)
    simpa [SimpleGraph.edgeFinset] using M.edgeSet.ncard_eq_toFinset_card hfinite
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.connected_planar_face_count_certificate__p2m_0a6cb8c8_85f4_4527_b550_0c59830e1a8e_a1
      M hM hcard hconn
  refine ⟨f, ?_, ?_⟩
  · rw [← hedge]
    omega
  · rw [← hedge]
    exact hfaces
