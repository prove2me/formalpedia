-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count_certificate__p2m_4ec6bc0b_ec8a_4e25_875f_9ac5631f6eca_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:17:31.639584+00:00
-- url     : https://prove2.me/submissions/76f5747a-fcf0-425e-ab1d-70775cf0bc64
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula__p2m_89410822_d74b_4a7e_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_facial_lengths__p2m_89410822_d74b_4a7e_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (f : ℕ) (length : Fin f → ℕ),
      Fintype.card V + f =
        (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 ∧
      2 * (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) =
        ∑ i, length i ∧
      ∀ i, 3 ≤ length i := by
  classical
  letI : DecidableRel G.Adj := dG
  obtain ⟨f, hf⟩ :=
    WilliamsonShmoys.planar_drawing_euler_formula__p2m_89410822_d74b_4a7e_a2
      G dG hG hConn
  have hfaces : f = G.edgeFinset.card + 2 - Fintype.card V := by omega
  subst f
  obtain ⟨length, hsum, hlength⟩ :=
    WilliamsonShmoys.planar_drawing_facial_lengths__p2m_89410822_d74b_4a7e_a2
      G dG hG hConn hcard
  exact ⟨_, length, by omega, hsum, hlength⟩
