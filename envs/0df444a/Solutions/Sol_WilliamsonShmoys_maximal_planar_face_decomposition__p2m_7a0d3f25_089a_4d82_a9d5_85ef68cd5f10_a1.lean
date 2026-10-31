-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_7a0d3f25_089a_4d82_a9d5_85ef68cd5f10_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:48:07.037609+00:00
-- url     : https://prove2.me/submissions/3157e122-c7cb-4792-b366-4e5f79c5c7f3

import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_and_incidence

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hMax : ∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = L) (hCard : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 ∧ 3 * f = 2 * L.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_euler_and_incidence L hL hMax hCard
