-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_drawable_supergraph__p2m_afa4574a_1607_44bb_93bd_58940dcb1487_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:11:42.76366+00:00
-- url     : https://prove2.me/submissions/446017bf-4b23-4fc9-bccc-cbfeac513356

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists__p2m_f0debea5_402c_48d1_9751_ec911f78abab_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_f0debea5_402c_48d1_9751_ec911f78abab_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    [DecidableRel M.Adj] (hcard : 3 ≤ Fintype.card V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, ∃ (hNdec : DecidableRel N.Adj),
      M ≤ N ∧ HasPlanarDrawingOn N ∧
        (letI : DecidableRel N.Adj := hNdec; N.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨N, hNdec, hMN, hNplanar, hNmax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_f0debea5_402c_48d1_9751_ec911f78abab_a1
      M hM
  refine ⟨N, hNdec, hMN, hNplanar, ?_⟩
  letI : DecidableRel N.Adj := hNdec
  exact WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_f0debea5_402c_48d1_9751_ec911f78abab_a1
    N hcard hNplanar hNmax