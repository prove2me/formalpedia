-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_b79a3d22_514c_40c6_b0d9_3192cd4e6368_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:04:36.979965+00:00
-- url     : https://prove2.me/submissions/3d18c1eb-76ab-4c9b-822d-ba8a3156154d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_0a2f9458_d7af_417f_8026_7751bf7a2ead_a1
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_finite__p2m_0a2f9458_d7af_417f_8026_7751bf7a2ead_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hK : HasPlanarDrawingOn K) :
    Exists (fun L : SimpleGraph V => Exists (fun dL : DecidableRel L.Adj =>
      And (LE.le K L) (And (HasPlanarDrawingOn L)
        (forall M : SimpleGraph V, forall dM : DecidableRel M.Adj,
          LE.le L M -> HasPlanarDrawingOn M -> LE.le M L)))) := by
  classical
  obtain ⟨L, hKL, hL, hmax⟩ := WilliamsonShmoys.exists_maximal_extension_finite__p2m_0a2f9458_d7af_417f_8026_7751bf7a2ead_a1 HasPlanarDrawingOn (by
    intro G H hGH hH
    exact WilliamsonShmoys.planar_drawing_subgraph__p2m_0a2f9458_d7af_417f_8026_7751bf7a2ead_a1 G H hGH hH) K hK
  exact ⟨L, Classical.decRel _, hKL, hL, fun M _ hLM hM => hmax M hLM hM⟩