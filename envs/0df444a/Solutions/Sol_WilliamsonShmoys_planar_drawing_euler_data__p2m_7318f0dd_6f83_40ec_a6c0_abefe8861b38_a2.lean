-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_data__p2m_7318f0dd_6f83_40ec_a6c0_abefe8861b38_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:07:46.763321+00:00
-- url     : https://prove2.me/submissions/0fd9791a-d632-49ec-a187-c589d1281a5d

import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_02b5c4aa_87bb_4609_924c_f8cb942a1930_a1
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_02b5c4aa_87bb_4609_924c_f8cb942a1930_a1
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨f, hf⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count__p2m_02b5c4aa_87bb_4609_924c_f8cb942a1930_a1
      G hG hconn
  have hbound :=
    WilliamsonShmoys.simple_planar_edge_bound__p2m_02b5c4aa_87bb_4609_924c_f8cb942a1930_a1
      G hG hconn hCard
  refine ⟨f, hf, ?_⟩
  omega