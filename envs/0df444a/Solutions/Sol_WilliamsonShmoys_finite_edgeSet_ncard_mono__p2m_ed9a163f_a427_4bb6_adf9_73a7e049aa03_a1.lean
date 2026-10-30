-- Prove2me | solution 1 for WilliamsonShmoys_finite_edgeSet_ncard_mono__p2m_ed9a163f_a427_4bb6_adf9_73a7e049aa03_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:31:49.77755+00:00
-- url     : https://prove2.me/submissions/f9fb20ac-ac06-4cf9-be28-b1431df6dd0d

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)