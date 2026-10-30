-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono__p2m_34984a32_89db_4d2f_ac2e_84ee95aee4c9_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:33.562645+00:00
-- url     : https://prove2.me/submissions/22efcd67-1993-4f33-93a7-94dd8ff46e53

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (M N : SimpleGraph V) (hMN : M ≤ N) :
    M.edgeSet.ncard ≤ N.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hMN)