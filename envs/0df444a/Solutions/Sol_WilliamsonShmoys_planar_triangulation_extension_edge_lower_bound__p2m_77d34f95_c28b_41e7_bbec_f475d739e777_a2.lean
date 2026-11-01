-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_edge_lower_bound__p2m_77d34f95_c28b_41e7_bbec_f475d739e777_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:52:16.354094+00:00
-- url     : https://prove2.me/submissions/eb0e4b67-61ea-440b-aa19-3237ee3c98bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_ea7a71ed_13b1_4c29_adb9_6de531e96387_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ea7a71ed_13b1_4c29_adb9_6de531e96387_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      K.edgeFinset ⊆ L.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 <= L.edgeFinset.card := by
  obtain ⟨L, dL, hsub, hplanar, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ea7a71ed_13b1_4c29_adb9_6de531e96387_a1
      K dK hK
  exact ⟨L, dL, hsub, hplanar,
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ea7a71ed_13b1_4c29_adb9_6de531e96387_a1
      L dL hplanar hcard hmax⟩