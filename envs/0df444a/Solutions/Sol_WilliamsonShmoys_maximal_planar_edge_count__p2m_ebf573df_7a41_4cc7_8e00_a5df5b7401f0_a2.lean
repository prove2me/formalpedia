-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_ebf573df_7a41_4cc7_8e00_a5df5b7401f0_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:09:30.270113+00:00
-- url     : https://prove2.me/submissions/a1d7528b-6cb7-4010-bc83-b89ca910e234
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_finite_drawings__p2m_f4d5f6b5_50cb_4a4f_bb2b_dbd916d0d942_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_f4d5f6b5_50cb_4a4f_bb2b_dbd916d0d942_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn N ->
      M.edgeFinset ⊆ N.edgeFinset -> N.edgeFinset ⊆ M.edgeFinset)
    (hcard : 3 <= Fintype.card V) :
    M.edgeFinset.card = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound_for_finite_drawings__p2m_f4d5f6b5_50cb_4a4f_bb2b_dbd916d0d942_a1 M dM hM hcard
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f4d5f6b5_50cb_4a4f_bb2b_dbd916d0d942_a1 M dM hM hmax hcard
  omega