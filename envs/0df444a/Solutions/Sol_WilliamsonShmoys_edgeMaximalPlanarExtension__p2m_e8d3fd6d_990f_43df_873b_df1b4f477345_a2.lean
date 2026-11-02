-- Prove2me | solution 1 for WilliamsonShmoys.edgeMaximalPlanarExtension__p2m_e8d3fd6d_990f_43df_873b_df1b4f477345_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:29:51.33113+00:00
-- url     : https://prove2.me/submissions/294897cb-63a3-4ddb-8ab7-f2f0fd541157

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_predicate_has_maximal__p2m_5e5b150a_02d6_4c7e_b48f_ee76aa630368_a3
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      HasPlanarDrawingOn K ∧
      (letI : DecidableRel H.Adj := dH
       letI : DecidableRel K.Adj := dK
       H.edgeFinset ⊆ K.edgeFinset) ∧
      ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        HasPlanarDrawingOn L →
        (letI : DecidableRel K.Adj := dK
         letI : DecidableRel L.Adj := dL
         K.edgeFinset ⊆ L.edgeFinset → L.edgeFinset ⊆ K.edgeFinset) := by
  classical
  let p : SimpleGraph V → Prop := fun G => HasPlanarDrawingOn G ∧ H ≤ G
  obtain ⟨K, hK, hKmax⟩ :=
    finite_predicate_has_maximal__p2m_5e5b150a_02d6_4c7e_b48f_ee76aa630368_a3
      p ⟨H, hH, le_rfl⟩
  refine ⟨K, inferInstance, hK.1, ?_, ?_⟩
  · simpa [SimpleGraph.edgeFinset_subset_edgeFinset] using hK.2
  · intro L dL hL hKL
    letI : DecidableRel K.Adj := inferInstance
    letI : DecidableRel L.Adj := dL
    have hKL' : K ≤ L :=
      (SimpleGraph.edgeFinset_subset_edgeFinset).1 hKL
    have hLP : p L := ⟨hL, hK.2.trans hKL'⟩
    have hLK : L ≤ K := hKmax L hLP hKL'
    exact (SimpleGraph.edgeFinset_subset_edgeFinset).2 hLK