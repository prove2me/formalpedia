-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_ecade84c_ffb2_4aac_a689_428692de6887_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:26:15.507527+00:00
-- url     : https://prove2.me/submissions/1b887b8b-301d-4005-a143-b23e9fdd5011
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_planar_supergraph__p2m_98915fb2_fad3_4066_b195_28760c9e8707_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_98915fb2_fad3_4066_b195_28760c9e8707_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V, Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧
      (letI : DecidableRel R.Adj := Classical.decRel R.Adj
       3 * Fintype.card V = R.edgeFinset.card + 6) := by
  obtain ⟨R, hQR, hR, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_98915fb2_fad3_4066_b195_28760c9e8707_a1 Q hQ
  refine ⟨R, hQR, hR, ?_⟩
  letI : DecidableRel R.Adj := Classical.decRel R.Adj
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_98915fb2_fad3_4066_b195_28760c9e8707_a1 R hR hcard hmax
  exact hcount.symm