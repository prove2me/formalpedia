-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_ade061e0_083b_4a3b_882e_6784f9579cdf_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:31:23.60998+00:00
-- url     : https://prove2.me/submissions/24521863-4b66-410d-be36-394ee03f67f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_2f707832_942f_4ae9_9944_7f0d941152ce_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition__p2m_2f707832_942f_4ae9_9944_7f0d941152ce_a1
      K hK hmax hV
  omega