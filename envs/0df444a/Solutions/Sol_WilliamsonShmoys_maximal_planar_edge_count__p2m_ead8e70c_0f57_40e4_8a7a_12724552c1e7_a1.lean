-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_ead8e70c_0f57_40e4_8a7a_12724552c1e7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:02:04.266806+00:00
-- url     : https://prove2.me/submissions/48f58948-0d4b-4076-8cc0-96e8facf0e0c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_1cbebd7a_cbfe_40cb_8e61_899ac9ec9081_a3
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    N.edgeFinset.card + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hK, hKd, htri⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_1cbebd7a_cbfe_40cb_8e61_899ac9ec9081_a3
      N hN hcard
  letI : DecidableRel K.Adj := hKd
  have hKN : K = N := hmax K hNK hK
  have hfin : K.edgeFinset = N.edgeFinset := by
    ext e
    simp [hKN]
  rw [← hfin]
  exact htri