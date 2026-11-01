-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_2ae65a7c_57f2_4cef_ba44_e42518b858bb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:27:29.588853+00:00
-- url     : https://prove2.me/submissions/c838f4d9-afee-4b45-9875-af903513f6bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension__p2m_9e7a2e08_df96_4db8_828f_8ffe40cd0bda_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_9e7a2e08_df96_4db8_828f_8ffe40cd0bda_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (dW : DecidableRel W.Adj)
    (hW : HasPlanarDrawingOn W)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (T : SimpleGraph V) (dT : DecidableRel T.Adj),
      HasPlanarDrawingOn T ∧
      (letI : DecidableRel W.Adj := dW
       letI : DecidableRel T.Adj := dT
       W.edgeFinset ⊆ T.edgeFinset) ∧
      (letI : DecidableRel T.Adj := dT
       T.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨T, dT, hT, hWT, hmax⟩ :=
    WilliamsonShmoys.planar_drawable_maximal_extension__p2m_9e7a2e08_df96_4db8_828f_8ffe40cd0bda_a1
      W dW hW
  exact ⟨T, dT, hT, hWT,
    WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_9e7a2e08_df96_4db8_828f_8ffe40cd0bda_a1
      T dT hT hn hmax⟩