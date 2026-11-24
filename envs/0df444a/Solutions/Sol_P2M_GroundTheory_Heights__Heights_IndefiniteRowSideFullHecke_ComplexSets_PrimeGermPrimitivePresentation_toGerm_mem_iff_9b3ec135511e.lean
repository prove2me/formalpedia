-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermPrimitivePresentation_toGerm_mem_iff_9b3ec135511e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:52.890869+00:00
-- url     : https://prove2.me/submissions/9220ccf5-4f7e-4527-b623-27cbf2d58276

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermCentredIntegralEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PrimitiveLinearForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermPrimitivePresentation_exists_of_mem_holGermIdeal_6e04f02e5a02

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
open Topology Filter Polynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermPrimitivePresentation
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermPrimitivePresentation
theorem _root_.solution {w : σ → ℂ} {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ} (hp : ∀ i, AnalyticAt ℂ (p i) w)
    (u : anFun w) : toGerm w u ∈ holGermIdeal w p ↔ IsGermCombination w p u.1 := by
  constructor
  · intro hu
    obtain ⟨h, hh, e⟩ := exists_of_mem_holGermIdeal p hu
    exact ⟨h, hh, Germ.coe_eq.1 e⟩
  · rintro ⟨h, hh, hev⟩
    have hsum : toGerm w u = ∑ i, toGerm w (mkA (h i) (hh i)) * toGerm w (mkA (p i) (hp i)) := by
      simp only [← map_mul, ← map_sum]
      apply Subtype.ext
      change ((u.1 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) =
        (((∑ i, mkA (h i) (hh i) * mkA (p i) (hp i) : anFun w) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
      refine Germ.coe_eq.2 (hev.mono fun z hz => ?_)
      simp [hz, Finset.sum_apply, mkA]
    rw [hsum]
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermPrimitivePresentation
