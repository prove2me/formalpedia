-- Prove2me | solution 1 for WilliamsonShmoys.connected_strictly_more_edges__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:13:34.336595+00:00
-- url     : https://prove2.me/submissions/bd1c4b7b-6ae8-4d1e-9932-ca4233d1a81a

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V) (hKH : K ≤ H)
    (hK : ¬ K.Connected) (hH : H.Connected) :
    K.edgeSet.ncard < H.edgeSet.ncard := by
  have hne : K ≠ H := by
    intro h
    exact hK (by simpa [h] using hH)
  have hlt : K < H := lt_of_le_of_ne hKH hne
  exact Set.ncard_lt_ncard (SimpleGraph.edgeSet_ssubset_edgeSet.mpr hlt)