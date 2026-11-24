-- Prove2me | solution 2 for WilliamsonShmoys.disconnected_planar_connected_augmentation__p2m_9e7a5396_2787_4caf_938c_608408887b08_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:25:59.389238+00:00
-- url     : https://prove2.me/submissions/0913cb32-b134-4894-8e3b-1cd187082a24

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_supergraph_of_disconnected_planar__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ H.Connected) :
    ∃ H' : SimpleGraph V,
      HasPlanarDrawingOn H' ∧ H'.Connected ∧
      H.edgeSet.ncard + 1 ≤ H'.edgeSet.ncard := by
  obtain ⟨K, -, hconn, hK, hcount⟩ :=
    WilliamsonShmoys.connected_supergraph_of_disconnected_planar__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2
      H hplanar hV hdisconnected
  exact ⟨K, hK, hconn, hcount⟩
