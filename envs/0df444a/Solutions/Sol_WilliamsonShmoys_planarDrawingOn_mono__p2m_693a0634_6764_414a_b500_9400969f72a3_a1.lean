-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_mono__p2m_693a0634_6764_414a_b500_9400969f72a3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:23:15.783289+00:00
-- url     : https://prove2.me/submissions/c0ae9790-d5d9-4c08-872b-421b83dd9e30

import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_of_edgeSet_subset

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G H : SimpleGraph V) (hGH : G.edgeSet ⊆ H.edgeSet) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : WilliamsonShmoys.HasPlanarDrawingOn G :=
  WilliamsonShmoys.hasPlanarDrawingOn_of_edgeSet_subset hH hGH
