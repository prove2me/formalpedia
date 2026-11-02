-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_91ffed91_b87b_43c6_ba27_69e25b4e372c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:59:50.220083+00:00
-- url     : https://prove2.me/submissions/0ff7ac28-f6a3-4cb3-ab11-d68ea85a5ce8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension__p2m_3b1a98e5_f0d3_4027_b8f6_4e4c1f675a8e_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    N.edgeFinset.card + 6 = 3 * Fintype.card V := by
  obtain ⟨P, hNP, hP, hcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_extension__p2m_3b1a98e5_f0d3_4027_b8f6_4e4c1f675a8e_a1
      N hN hconn hcard
  have hPN : P = N := hmax P hNP hP
  subst P
  exact hcount