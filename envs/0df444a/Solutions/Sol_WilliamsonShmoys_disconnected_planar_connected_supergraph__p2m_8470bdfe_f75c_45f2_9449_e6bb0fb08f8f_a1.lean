-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_connected_supergraph__p2m_8470bdfe_f75c_45f2_9449_e6bb0fb08f8f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:42:15.256681+00:00
-- url     : https://prove2.me/submissions/4a409645-db22-469e-a8d1-b0008624a8b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_strict_extension__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ K ≠ G ∧ HasPlanarDrawingOn K ∧ K.Connected := by
  obtain ⟨K, hGK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1
      G hplanar
  have hKconnected : K.Connected := by
    by_contra hKdisconnected
    obtain ⟨L, hKL, hLK, hLplanar⟩ :=
      WilliamsonShmoys.disconnected_planar_strict_extension__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1
        K hKplanar (by omega) hKdisconnected
    exact hLK (hKmax L hKL hLplanar)
  refine ⟨K, hGK, ?_, hKplanar, hKconnected⟩
  intro hKG
  apply hdisconnected
  simpa [hKG] using hKconnected