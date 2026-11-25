-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_sum_truncCoord_one_d40575ce1942
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:05.639478+00:00
-- url     : https://prove2.me/submissions/5e5fa6b5-85d1-4c46-af81-8ed1799da395

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagLineSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionForms

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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω]
  {F : Type*} [Field F] [Algebra F Ω] {N M : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
  {Φ : Type*} [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
theorem _root_.solution (t : Fin N → Φ) (h0 : 0 < N) (z : Fin N → Φ) :
    ∑ i, truncCoord t 1 i * z i = t ⟨0, h0⟩ * z ⟨0, h0⟩ := by
  rw [Finset.sum_eq_single ⟨0, h0⟩]
  · simp [truncCoord]
  · intro j _ hj
    have : ¬ (j : ℕ) < 1 := by
      intro h; apply hj; ext; simp; omega
    simp [truncCoord, this]
  · simp
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
