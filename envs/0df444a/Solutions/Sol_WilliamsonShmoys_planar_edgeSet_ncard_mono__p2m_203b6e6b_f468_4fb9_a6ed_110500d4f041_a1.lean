-- Prove2me | solution 1 for WilliamsonShmoys_planar_edgeSet_ncard_mono__p2m_203b6e6b_f468_4fb9_a6ed_110500d4f041_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:54:01.374163+00:00
-- url     : https://prove2.me/submissions/ccbd017b-0d7b-4bfa-9554-9709cb3332b9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] (G H : SimpleGraph V) (hsub : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hsub)