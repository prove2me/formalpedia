-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_edge_count__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:53:01.599498+00:00
-- url     : https://prove2.me/submissions/e173dbfc-6a37-4e29-babf-a881c667c50c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_face_count__p2m_a5abbcfc_8844_40a4_806c_eef213b4f62c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangular_face_incidence__p2m_a5abbcfc_8844_40a4_806c_eef213b4f62c_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys_maximal_planar_euler_face_count__p2m_a5abbcfc_8844_40a4_806c_eef213b4f62c_a1
      H hHplanar hconn
  have hInc :=
    WilliamsonShmoys_maximal_planar_triangular_face_incidence__p2m_a5abbcfc_8844_40a4_806c_eef213b4f62c_a1
      G H hGH hHplanar hmax hV hconn f hEuler
  omega