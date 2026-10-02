-- Prove2me | solution 1 for ProcessingNetworks.Subcriticality.stable_for_all_subcritical_implies_maximally_stable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T00:44:28.522844+00:00
-- url     : https://prove2.me/submissions/2e4bbd01-5d43-4a36-97e4-70f1ff64d5a6

import Mathlib
import Definitions.Def_ProcessingNetworks_Subcriticality_SPNPlanningData
import Definitions.Def_ProcessingNetworks_Subcriticality_StaticPlanningProblem
import Definitions.Def_ProcessingNetworks_Subcriticality_MaximalStability

set_option autoImplicit false

open ProcessingNetworks.Subcriticality in
theorem solution
    {I J K : ℕ} {Policy : Type*} (D : SPNPlanningData I J K)
    (PolicyStable : Policy → (Fin I → ℝ) → Prop)
    (hΛstar_subset_Λ : StabilityRegion PolicyStable ⊆ SubcriticalRegion D)
    (p : Policy) (hp : ∀ lam ∈ SubcriticalRegion D, PolicyStable p lam) :
    IsMaximallyStable PolicyStable p := by
  intro lam hlam
  exact hp lam (hΛstar_subset_Λ hlam)
