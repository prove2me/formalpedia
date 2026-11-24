-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_exists_bound_pairs_7ea5a7f18a7c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:39.223083+00:00
-- url     : https://prove2.me/submissions/d02ba1cf-4654-41e0-95e8-d63570b11271

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreDiscriminantHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreDiscriminantHolomorphic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
variable {σ : Type} [Fintype σ]
omit [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
theorem _root_.solution {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {K : Set (Fin d → ℂ)} (l : (σ → ℂ) →L[ℂ] ℂ) (hK : IsCompact {x | x ∈ Y ∧ A x ∈ K}) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ {x | x ∈ Y ∧ A x ∈ K}, ∀ b ∈ {x | x ∈ Y ∧ A x ∈ K}, ‖l a - l b‖ ≤ C := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn l.continuous.continuousOn
  refine ⟨2 * |M| + 1, by have := abs_nonneg M; linarith, fun a ha b hb => ?_⟩
  calc ‖l a - l b‖ ≤ ‖l a‖ + ‖l b‖ := norm_sub_le _ _
    _ ≤ 2 * |M| + 1 := by
      have := hM a ha
      have := hM b hb
      have := le_abs_self M
      linarith
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
