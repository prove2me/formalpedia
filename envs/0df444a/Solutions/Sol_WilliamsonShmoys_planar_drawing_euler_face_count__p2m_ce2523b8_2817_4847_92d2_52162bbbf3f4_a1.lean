-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count__p2m_ce2523b8_2817_4847_92d2_52162bbbf3f4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:58:05.799159+00:00
-- url     : https://prove2.me/submissions/fba2085b-e717-463b-b148-35f81d1a745c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_euler_face_count__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected) :
    ∃ f : ℕ, Fintype.card V + f = M.edgeFinset.card + 2 := by
  obtain ⟨f, hf⟩ :=
    WilliamsonShmoys.euler_face_count__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1
      M hM hconn
  refine ⟨f, ?_⟩
  simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using hf
