-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulation_maximal_extension__p2m_c8388ff0_77e3_49f1_bb1d_428d2f9c95cd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:26:33.462935+00:00
-- url     : https://prove2.me/submissions/7f024c95-2795-4661-b0a9-4713a55de686

import Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph_completion

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧ ∀ G : SimpleGraph V, H ≤ G → HasPlanarDrawingOn G → G = H :=
  WilliamsonShmoys.finite_maximal_drawable_supergraph_completion K hK
