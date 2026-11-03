-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_disconnected_extension__p2m_46bd3770_49b2_4c1a_90e5_69dd719cc31d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:13:16.421428+00:00
-- url     : https://prove2.me/submissions/4d7873db-7b53-44aa-81b1-b68cb4ad5c88

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2932b977_69eb_43f4_aaa9_a9ebd474ac36_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : ¬ K.Connected) :
    ∃ x y : V, ∃ L : SimpleGraph V,
      x ≠ y ∧ ¬ K.Adj x y ∧ K ≤ L ∧ L.Adj x y ∧
        WilliamsonShmoys.HasPlanarDrawingOn L := by
  obtain ⟨L, hKL, hLconn, hLplanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_2932b977_69eb_43f4_aaa9_a9ebd474ac36_a2
      K hcard hK
  have hnew : ∃ x y : V, L.Adj x y ∧ ¬ K.Adj x y := by
    by_contra h
    push_neg at h
    have heq : L = K := by
      ext x y
      constructor
      · intro hxy
        exact h x y hxy
      · intro hxy
        exact hKL hxy
    subst L
    exact hconn hLconn
  obtain ⟨x, y, hxy, hnot⟩ := hnew
  exact ⟨x, y, L, hxy.ne, hnot, hKL, hxy, hLplanar⟩