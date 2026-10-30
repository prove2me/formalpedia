-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_certificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:50:48.83649+00:00
-- url     : https://prove2.me/submissions/935a31e7-092c-45d6-a584-dc19897c8484
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_53c17418_11ef_424f_a50a_b8723b415e73_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_has_face_certificate__p2m_53c17418_11ef_424f_a50a_b8723b415e73_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    Nonempty (WilliamsonShmoys.PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3 H) := by
  obtain ⟨K, hHK, hKDraw, hKMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_53c17418_11ef_424f_a50a_b8723b415e73_a2 H hDraw
  have hKMax' : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
    intro L hKL hLDraw
    exact hKMax L (le_trans hHK hKL) hLDraw
  obtain ⟨cK⟩ :=
    WilliamsonShmoys.maximal_planar_has_face_certificate__p2m_53c17418_11ef_424f_a50a_b8723b415e73_a2 K hKDraw hKMax' hV
  refine ⟨{ cK with contains := ?_ }⟩
  intro u v huv
  exact cK.contains (hHK huv)
