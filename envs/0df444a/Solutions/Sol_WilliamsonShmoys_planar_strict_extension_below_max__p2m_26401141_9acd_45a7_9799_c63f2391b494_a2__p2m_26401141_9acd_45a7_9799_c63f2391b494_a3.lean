-- Prove2me | solution 1 for WilliamsonShmoys.planar_strict_extension_below_max__p2m_26401141_9acd_45a7_9799_c63f2391b494_a2__p2m_26401141_9acd_45a7_9799_c63f2391b494_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:42:53.736248+00:00
-- url     : https://prove2.me/submissions/6e4f8fd7-c0a9-4e5e-90f8-94b69b655cb4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_07b4009a_04ca_4342_a9d5_b274d08c0821_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_07b4009a_04ca_4342_a9d5_b274d08c0821_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ H : SimpleGraph V, DecidableRel H.Adj :=
      fun H => Classical.decRel H.Adj
    G.edgeFinset.card < 3 * Fintype.card V - 6 →
    ∃ H : SimpleGraph V,
      G.edgeFinset ⊆ H.edgeFinset ∧
      HasPlanarDrawingOn H ∧
      ¬ H.edgeFinset ⊆ G.edgeFinset := by
  letI : ∀ H : SimpleGraph V, DecidableRel H.Adj :=
    fun H => Classical.decRel H.Adj
  intro hlt
  obtain ⟨H, hsub, hH, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph__p2m_07b4009a_04ca_4342_a9d5_b274d08c0821_a1 G hG
  have hHcard :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_07b4009a_04ca_4342_a9d5_b274d08c0821_a1 H hH hcard hmax
  refine ⟨H, hsub, hH, ?_⟩
  intro hback
  have heq : G.edgeFinset = H.edgeFinset := Finset.Subset.antisymm hsub hback
  have hcards := congrArg Finset.card heq
  omega