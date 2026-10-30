-- Prove2me | solution 1 for WilliamsonShmoys_finite_planar_supergraph_maximal__p2m_9b3efef9_88d6_4457_a3f3_6508d18ac1de_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:12:14.016165+00:00
-- url     : https://prove2.me/submissions/472ce2f0-9883-4617-a182-4d3eb20a4888

import Theorems.Thm_finite_simpleGraph_maximal_supergraph__p2m_1841e8f3_3dc0_4413_8d65_8f642645b455_a2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGplanar : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun K : SimpleGraph V => And (LE.le G K) (And (WilliamsonShmoys.HasPlanarDrawingOn K)
      (∀ L : SimpleGraph V, LE.le K L → WilliamsonShmoys.HasPlanarDrawingOn L → LE.le L K)) := by
  exact finite_simpleGraph_maximal_supergraph__p2m_1841e8f3_3dc0_4413_8d65_8f642645b455_a2
    G WilliamsonShmoys.HasPlanarDrawingOn hGplanar