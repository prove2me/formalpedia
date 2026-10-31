-- Prove2me | solution 1 for WilliamsonShmoys_planar_edge_augmentation__p2m_2508ece6_24ff_4a9a_9901_7572a4f15f41_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:06:08.215784+00:00
-- url     : https://prove2.me/submissions/e7575d83-d0ff-45f1-80d3-536d48149b8b

import Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximal__p2m_9b3efef9_88d6_4457_a3f3_6508d18ac1de_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9b3efef9_88d6_4457_a3f3_6508d18ac1de_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hGplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : LE.le 3 (Fintype.card V))
    (hsmall : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    Exists fun K : SimpleGraph V => And (LE.le G K) (And (WilliamsonShmoys.HasPlanarDrawingOn K) (Not (LE.le K G))) := by
  obtain ⟨K, hGK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys_finite_planar_supergraph_maximal__p2m_9b3efef9_88d6_4457_a3f3_6508d18ac1de_a2
      (V := V) G hGplanar
  have hKcount :=
    WilliamsonShmoys_maximal_planar_edge_count__p2m_9b3efef9_88d6_4457_a3f3_6508d18ac1de_a2
      (V := V) K hKplanar hKmax hV
  refine ⟨K, hGK, hKplanar, ?_⟩
  intro hKG
  have hEq : K = G := le_antisymm hKG hGK
  have hcardEq : K.edgeSet.ncard = G.edgeSet.ncard :=
    congrArg (fun H : SimpleGraph V => H.edgeSet.ncard) hEq
  omega