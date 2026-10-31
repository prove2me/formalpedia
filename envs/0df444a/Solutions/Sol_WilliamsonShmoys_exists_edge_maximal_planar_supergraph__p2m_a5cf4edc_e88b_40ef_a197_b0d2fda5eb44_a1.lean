-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:27:41.940771+00:00
-- url     : https://prove2.me/submissions/53524599-69c8-47d4-b070-72710cadbf7c

import Theorems.Thm_WilliamsonShmoys_drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L :=
  WilliamsonShmoys.drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1 K hK
