-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_eq__p2m_fda861fd_855b_4561_971f_8551142822a0_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:51:47.538365+00:00
-- url     : https://prove2.me/submissions/27faad25-aed5-4b8d-af45-ffbaf6dffd76
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_completion__p2m_162d43c0_0ffc_4e97_9a3b_e80d1c26e109_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn Q)
    (hMax : ∀ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet → HasPlanarDrawingOn R → R = Q)
    (hV : 3 ≤ Fintype.card V) : Q.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨R, hSub, hDrawR, hCount⟩ :=
    WilliamsonShmoys.maximal_planar_triangulation_completion__p2m_162d43c0_0ffc_4e97_9a3b_e80d1c26e109_a2
      Q hDraw hV
  have hRQ : R = Q := hMax R hSub hDrawR
  subst R
  exact hCount