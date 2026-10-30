-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:54:55.114179+00:00
-- url     : https://prove2.me/submissions/bd524be0-9fcb-48c9-b7ab-d8ca9d0a46ce

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_maximal_extension__p2m_726cc9ac_cced_4064_8c59_8a0717aa0ea1_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.Connected ∧
      (∀ (L : SimpleGraph V),
        (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  obtain ⟨K, hHK, hK, hmax, hcount⟩ :=
    WilliamsonShmoys.exists_planar_maximal_extension__p2m_726cc9ac_cced_4064_8c59_8a0717aa0ea1_a1 H hH
  exact ⟨K, hHK, hK, hconn.mono hHK, hmax, hcount⟩