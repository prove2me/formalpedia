-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_9bfda91a_9bda_408b_a2fd_6ab368fb7e28_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:46:32.175879+00:00
-- url     : https://prove2.me/submissions/22f233c4-0af7-43b4-8dd7-c3afd7dcd978
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_completion__p2m_40aa9783_d5dc_4892_8943_41fc2fc5d139_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn K)
    (hmax : ∀ J : SimpleGraph V, K.edgeSet ⊆ J.edgeSet →
      HasPlanarDrawingOn J → J.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hsub, hdraw, hcount⟩ :=
    WilliamsonShmoys.planar_graph_triangulation_completion__p2m_40aa9783_d5dc_4892_8943_41fc2fc5d139_a1
      K hcard hplanar
  have hJsub : J.edgeSet ⊆ K.edgeSet := hmax J hsub hdraw
  have heq : J.edgeSet = K.edgeSet := Set.Subset.antisymm hJsub hsub
  have hn : J.edgeSet.ncard = K.edgeSet.ncard := by
    exact congrArg (fun s : Set (Sym2 V) => s.ncard) heq
  omega