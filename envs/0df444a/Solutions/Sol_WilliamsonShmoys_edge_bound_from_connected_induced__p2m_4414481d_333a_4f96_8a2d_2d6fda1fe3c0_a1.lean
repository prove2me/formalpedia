-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_from_connected_induced__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:08:05.913167+00:00
-- url     : https://prove2.me/submissions/9b65a24a-2b14-4ec6-abfa-62c5174f8db0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_component_edge_data__p2m_66ed8684_7720_4905_99a4_14d61ffeb91a_a1
import Theorems.Thm_WilliamsonShmoys_sum_component_edge_bounds__p2m_66ed8684_7720_4905_99a4_14d61ffeb91a_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hLocal : ∀ (S : Finset V), 3 ≤ S.card →
      (L.induce (↑S : Set V)).Connected →
      (L.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  letI : Fintype L.ConnectedComponent := Fintype.ofFinite _
  obtain ⟨n, e, hsumV, hsumE, hpos, hsmall, hlarge⟩ :=
    WilliamsonShmoys.component_edge_data__p2m_66ed8684_7720_4905_99a4_14d61ffeb91a_a1
      L hLocal
  have htotal : 3 ≤ ∑ c : L.ConnectedComponent, n c := by
    simpa [hsumV] using hV
  have hagg :=
    WilliamsonShmoys.sum_component_edge_bounds__p2m_66ed8684_7720_4905_99a4_14d61ffeb91a_a1
      n e hpos htotal hsmall hlarge
  simpa [hsumV, hsumE] using hagg