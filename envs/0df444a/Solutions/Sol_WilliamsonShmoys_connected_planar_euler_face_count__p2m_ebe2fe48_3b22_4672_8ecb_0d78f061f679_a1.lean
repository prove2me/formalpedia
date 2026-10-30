-- Prove2me | solution 1 for WilliamsonShmoys_connected_planar_euler_face_count__p2m_ebe2fe48_3b22_4672_8ecb_0d78f061f679_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:08:04.39499+00:00
-- url     : https://prove2.me/submissions/87585c2a-3047-4691-aeb6-61420d1cbd73

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_for_face_accounting_57972424
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hConnected : G.Connected) :
    ∃ f : ℕ, f + Fintype.card V = G.edgeSet.ncard + 2 := by
  obtain ⟨f, hf⟩ :=
    WilliamsonShmoys.planar_drawing_euler_for_face_accounting_57972424
      G hG hConnected
  exact ⟨f, by simpa [Nat.add_comm] using hf⟩