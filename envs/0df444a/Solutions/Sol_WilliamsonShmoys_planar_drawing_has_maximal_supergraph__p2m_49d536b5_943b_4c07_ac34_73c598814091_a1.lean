-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_49d536b5_943b_4c07_ac34_73c598814091_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:45:50.930537+00:00
-- url     : https://prove2.me/submissions/4403a4b7-8825-4a13-938d-bebac3bbbe1f

import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_ddfe16f2_466b_4eda_98ed_20e5107df448_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hDraw : HasPlanarDrawingOn S) : ∃ T : SimpleGraph V, S ≤ T ∧ HasPlanarDrawingOn T ∧ ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T :=
  WilliamsonShmoys.maximal_planar_extension__p2m_ddfe16f2_466b_4eda_98ed_20e5107df448_a1 S hDraw
