-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_drawable_supergraph__p2m_80c37abd_a278_4e21_90d9_d42081afbb20_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:04:27.97377+00:00
-- url     : https://prove2.me/submissions/2aaa5b70-3af1-416b-b90a-35471f7f5841

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_edge_count__p2m_f3d5ae7b_e757_4e01_bdda_63180755b949_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hR : HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      (∀ u v, R.Adj u v → S.Adj u v) ∧
      HasPlanarDrawingOn S ∧
      (letI : DecidableRel R.Adj := Classical.decRel R.Adj
       letI : DecidableRel S.Adj := Classical.decRel S.Adj
       R.edgeFinset.card ≤ S.edgeFinset.card ∧
       S.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  classical
  obtain ⟨S, hS, hsub, hcount⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_edge_count__p2m_f3d5ae7b_e757_4e01_bdda_63180755b949_a1
      R hR hcard
  have hcardEq : S.edgeFinset.card = S.edgeSet.ncard := by
    have hco : (S.edgeFinset : Set (Sym2 V)) = S.edgeSet := by
      ext e
      simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    rw [← hco]
    rw [Set.ncard_coe_finset]
  refine ⟨S, ?_, hS, ?_⟩
  · intro u v huv
    apply S.mem_edgeSet.mp
    apply hsub
    exact R.mem_edgeSet.mpr huv
  · have hfinset : R.edgeFinset ⊆ S.edgeFinset := by
      intro e he
      apply SimpleGraph.mem_edgeFinset.mpr
      apply hsub
      exact SimpleGraph.mem_edgeFinset.mp he
    constructor
    · exact Finset.card_le_card hfinset
    · rw [hcardEq]
      exact hcount
