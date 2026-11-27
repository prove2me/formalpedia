-- Prove2me | solution 1 for SPFacilityGraph.lemma_Q_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:02:50.739599+00:00
-- url     : https://prove2.me/submissions/a6d13ab7-7abf-4be5-ac56-8c40b3e0eb0f

import Mathlib
import Theorems.Thm_SPFacilityGraph_attribution_of_lipschitz
import Theorems.Thm_SPFacilityGraph_sp_onto_lipschitz
import Theorems.Thm_SPFacilityGraph_sp_onto_finite_values

set_option autoImplicit false

open SPFacilityGraph

theorem solution {k n : ℕ} (hn : 2 ≤ n) (G : MetricGraph k)
    (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M) :
    ∃ (W : Finset G.Pt) (K : Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k))),
      IsEdgeTriangulation G n K ∧ HasDetAttribution G M W K := by
  obtain ⟨W, hW⟩ := sp_onto_finite_values hn G M hSP hM
  obtain ⟨K, hK⟩ := attribution_of_lipschitz G M W (sp_onto_lipschitz hn G M hSP hM) hW
  exact ⟨W, K, hK⟩
