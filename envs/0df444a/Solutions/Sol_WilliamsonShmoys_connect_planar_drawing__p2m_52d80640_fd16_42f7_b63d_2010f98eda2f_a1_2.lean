-- Prove2me | solution 2 for WilliamsonShmoys.connect_planar_drawing__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T09:32:25.877663+00:00
-- url     : https://prove2.me/submissions/6ea30d11-60ea-4ded-986d-2b68c69c8b94

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.planar_connected_supergraph__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
    K hK hV
