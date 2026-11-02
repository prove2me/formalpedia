-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_9a3366a6_4a3c_4f33_8539_99f470118709_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:01:40.183288+00:00
-- url     : https://prove2.me/submissions/651a6587-3b62-4d1e-bcf4-1909b0bf1d05

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_property__p2m_d747e68f_4b38_43ce_8028_cff46ecd3e2f_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L) (hcard : 3 <= Fintype.card V) :
    exists (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      L <= M /\ HasPlanarDrawingOn M /\
        forall (N : SimpleGraph V) (dN : DecidableRel N.Adj),
          M <= N -> HasPlanarDrawingOn N -> N = M := by
  classical
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_supergraph_for_property__p2m_d747e68f_4b38_43ce_8028_cff46ecd3e2f_a2
      L (fun G => HasPlanarDrawingOn G) hL
  let dM : DecidableRel M.Adj := Classical.decRel M.Adj
  exact ⟨M, dM, hLM, hM, fun N dN hMN hN => hmax N hMN hN⟩