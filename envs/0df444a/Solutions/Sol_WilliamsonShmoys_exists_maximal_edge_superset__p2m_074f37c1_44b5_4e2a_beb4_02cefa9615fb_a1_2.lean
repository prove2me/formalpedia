-- Prove2me | solution 2 for WilliamsonShmoys.exists_maximal_edge_superset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:37:34.079483+00:00
-- url     : https://prove2.me/submissions/c17d21b6-c1ad-4b85-88d1-357c4a2e3bb5

import Theorems.Thm_WilliamsonShmoys_exists_maximal_edge_superset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ K : SimpleGraph V,
      H.edgeFinset ⊆ K.edgeFinset ∧
      P K ∧
      ∀ G : SimpleGraph V, K.edgeFinset ⊆ G.edgeFinset → P G → G = K :=
  WilliamsonShmoys.exists_maximal_edge_superset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a2 H P hP