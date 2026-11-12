-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P81.strong_iff_joint
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T22:32:43.601191+00:00
-- url     : https://prove2.me/submissions/cd35adb5-348e-414f-bf4e-537822d90b79

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P81

noncomputable section

open scoped BigOperators ComplexConjugate Manifold ContDiff

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [hilbertComplete : CompleteSpace H]

section Lie

variable {m : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [lieCharts : ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
  [lieSmooth : LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G]
  [lieHausdorff : T2Space G] [lieSecondCountable : SecondCountableTopology G]

include hilbertComplete lieCharts lieSmooth lieHausdorff lieSecondCountable

theorem solution (U : G → H ≃ₗᵢ[ℂ] H) :
    Continuous (fun p : G × H => U p.1 p.2) ↔ (∀ v : H, Continuous (fun g => U g v)) := by
  constructor
  · intro h v
    exact h.comp (Continuous.prodMk_left v)
  · intro h
    rw [continuous_iff_continuousAt]
    rintro ⟨g0, v0⟩
    refine Metric.tendsto_nhds.2 (fun ε hε => ?_)
    have h1 : ∀ᶠ g in nhds g0, dist (U g v0) (U g0 v0) < ε / 2 :=
      Metric.tendsto_nhds.1 ((h v0).continuousAt) (ε / 2) (by linarith)
    have h2 : ∀ᶠ v in nhds v0, dist v v0 < ε / 2 :=
      Metric.tendsto_nhds.1 (continuousAt_id) (ε / 2) (by linarith)
    rw [nhds_prod_eq]
    filter_upwards [h1.prod_mk h2] with q hq
    obtain ⟨hq1, hq2⟩ := hq
    have htri := dist_triangle (U q.1 q.2) (U q.1 v0) (U g0 v0)
    have hiso : dist (U q.1 q.2) (U q.1 v0) = dist q.2 v0 := (U q.1).dist_map q.2 v0
    show dist (U q.1 q.2) (U g0 v0) < ε
    linarith

end Lie

end Hilbert

end
