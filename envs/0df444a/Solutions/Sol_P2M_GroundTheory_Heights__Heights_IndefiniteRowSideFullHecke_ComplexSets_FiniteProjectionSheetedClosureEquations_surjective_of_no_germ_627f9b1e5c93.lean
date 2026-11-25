-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteProjectionSheetedClosureEquations_surjective_of_no_germ_627f9b1e5c93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:32:08.191317+00:00
-- url     : https://prove2.me/submissions/b34326f5-ad39-4fbe-ab7e-31e88f90ed83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionSheetedClosureEquations
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionProperBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperSheetedFibreEsymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGridProductLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionSheetedClosureEquations

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
open Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FiniteProjectionSheetedClosureEquations
theorem _root_.solution {σ : Type} [Fintype σ] {d : ℕ}
    {w : σ → ℂ} {X : Set (σ → ℂ)} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (hA : ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) : Function.Surjective A := by
  by_contra hns
  have hlt : LinearMap.range (A : (σ → ℂ) →ₗ[ℂ] (Fin d → ℂ)) < ⊤ :=
    lt_top_iff_ne_top.2 fun htop => hns (by simpa using LinearMap.range_eq_top.1 htop)
  obtain ⟨f, hf0, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hfA : ∀ z, f (A z) = 0 := fun z => by
    have : f (A z) ∈ (LinearMap.range (A : (σ → ℂ) →ₗ[ℂ] (Fin d → ℂ))).map f := ⟨A z, ⟨z, rfl⟩, rfl⟩
    rw [hfmap] at this
    exact this
  have hev := hA (fun y => LinearMap.toContinuousLinearMap f y)
    ((LinearMap.toContinuousLinearMap f).analyticAt _)
    (Eventually.of_forall fun z _ => by simpa using hfA z)
  apply hf0
  have hker : LinearMap.ker f = ⊤ := by
    apply Submodule.eq_top_of_nonempty_interior'
    refine ⟨A w, mem_interior_iff_mem_nhds.2 ?_⟩
    filter_upwards [hev] with y hy
    simpa using hy
  exact LinearMap.ker_eq_top.1 hker
end FiniteProjectionSheetedClosureEquations
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
