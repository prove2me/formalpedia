-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_adapted_77e9c8dbc8e4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:22.26444+00:00
-- url     : https://prove2.me/submissions/840fd8b0-73d5-40a6-8f67-e3b50f7cf43a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω] {F : Type*} [Field F]
  [Algebra F Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
theorem _root_.solution (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (i : Fin N) :
    ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = chartZ y c (b i) := by
  have h : chartZ y c (b i) ∈ degLat F y (b i) c := ⟨1, one_mem _, by simp [chartZ]⟩
  rw [← hB.graded c hc i] at h
  obtain ⟨v, hv, h1, h2⟩ := h
  exact ⟨v, hv, h1, h2⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
