-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_3b0cc7ba_e438_41c2_b251_7b0cfc52f510_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:25:22.376102+00:00
-- url     : https://prove2.me/submissions/28b947de-2c7f-47cd-8fea-9e2e5410755e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound__p2m_3c202fe3_e8d7_442a_bae3_52d08143dac3_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M <= L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      3 * Fintype.card V <= L.edgeFinset.card + 6) := by
  obtain ⟨T, hLT, hT, hbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_bound__p2m_3c202fe3_e8d7_442a_bae3_52d08143dac3_a1
      L hL hcard
  have hTL : T <= L := hmax T hLT hT
  have hEq : T = L := le_antisymm hTL hLT
  subst T
  simpa using hbound