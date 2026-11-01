-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a1__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:29:44.328198+00:00
-- url     : https://prove2.me/submissions/84db2681-7df4-415d-a9c9-c21f59e4ffe6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_partialOrder_has_maximal_for_predicate__p2m_a870ea81_7152_406d_9ca9_18eedb61291e_a1

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite _
  let P : SimpleGraph V → Prop := fun K =>
    G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  letI : DecidablePred P := Classical.decPred P
  have hne : ∃ K : SimpleGraph V, P K := ⟨G, le_rfl, hG⟩
  obtain ⟨K, hK, hmax⟩ :=
    finite_partialOrder_has_maximal_for_predicate__p2m_a870ea81_7152_406d_9ca9_18eedb61291e_a1 P hne
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  apply hmax L
  · exact ⟨le_trans hK.1 hKL, hL⟩
  · exact hKL