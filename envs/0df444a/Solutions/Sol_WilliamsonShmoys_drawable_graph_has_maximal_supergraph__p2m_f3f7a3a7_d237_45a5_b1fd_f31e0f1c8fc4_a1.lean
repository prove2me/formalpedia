-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_maximal_supergraph__p2m_f3f7a3a7_d237_45a5_b1fd_f31e0f1c8fc4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:50:19.12485+00:00
-- url     : https://prove2.me/submissions/49afcb4d-c8b8-44e0-8c5c-bd663ba73701

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn K) :
    ∃ J : SimpleGraph V, K.edgeSet ⊆ J.edgeSet ∧
      HasPlanarDrawingOn J ∧
      ∀ L : SimpleGraph V, J.edgeSet ⊂ L.edgeSet → ¬ HasPlanarDrawingOn L := by
  classical
  let S : Set (SimpleGraph V) := {J | K ≤ J ∧ HasPlanarDrawingOn J}
  have hS : S.Nonempty := ⟨K, le_rfl, hplanar⟩
  obtain ⟨J, hJ, hmax⟩ := (Set.toFinite S).exists_maximal hS
  refine ⟨J, SimpleGraph.edgeSet_subset_edgeSet.mpr hJ.1, hJ.2, ?_⟩
  intro L hJL hL
  have hlt : J < L := SimpleGraph.edgeSet_ssubset_edgeSet.mp hJL
  have hKL : K ≤ L := hJ.1.trans hlt.le
  have hLmem : L ∈ S := ⟨hKL, hL⟩
  have hLJ : L ≤ J := hmax hLmem hlt.le
  exact (not_le_of_gt hlt) hLJ