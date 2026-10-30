-- Prove2me | solution 1 for SimpleGraph.edgeSet_ncard_mono__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:41:11.52536+00:00
-- url     : https://prove2.me/submissions/88e48c89-0684-45b3-b24a-fbdb41bb166c

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (G H : SimpleGraph V) (hGH : G ≤ H) : G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite H.edgeSet)