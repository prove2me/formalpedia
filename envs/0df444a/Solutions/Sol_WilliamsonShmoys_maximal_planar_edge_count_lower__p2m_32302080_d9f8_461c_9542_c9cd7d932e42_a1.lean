-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_32302080_d9f8_461c_9542_c9cd7d932e42_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T07:37:46.851194+00:00
-- url     : https://prove2.me/submissions/81cb81b6-3252-416d-b28c-489cfd60e0fe

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_inclusionMaximalPlanarDrawingOn_edgeSet_ncard_ge

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hR : HasPlanarDrawingOn R)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ S : SimpleGraph V, R ≤ S → HasPlanarDrawingOn S → S = R) :
    ∀ [hRdec : DecidableRel R.Adj],
      3 * Fintype.card V - 6 ≤ R.edgeFinset.card := by
  intro hRdec
  have hbound :
      3 * Fintype.card V - 6 ≤ R.edgeSet.ncard :=
    WilliamsonShmoys.inclusionMaximalPlanarDrawingOn_edgeSet_ncard_ge
      R hcard hR hmax
  have htoFinset :
      (Set.toFinite R.edgeSet).toFinset = R.edgeFinset := by
    ext e
    simp [SimpleGraph.edgeFinset]
  have hedge :
      R.edgeSet.ncard = R.edgeFinset.card := by
    calc
      R.edgeSet.ncard =
          (Set.toFinite R.edgeSet).toFinset.card :=
        Set.ncard_eq_toFinset_card R.edgeSet (Set.toFinite R.edgeSet)
      _ = R.edgeFinset.card := by rw [htoFinset]
  rw [← hedge]
  exact hbound

