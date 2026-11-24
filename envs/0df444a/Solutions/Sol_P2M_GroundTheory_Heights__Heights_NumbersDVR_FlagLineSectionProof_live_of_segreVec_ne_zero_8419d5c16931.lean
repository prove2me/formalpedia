-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_live_of_segreVec_ne_zero_8419d5c16931
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:22.30118+00:00
-- url     : https://prove2.me/submissions/4fbc834f-8754-479b-8220-a365dbe55e26

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
theorem _root_.solution {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : segreVec y c ≠ 0) :
    ∀ k, y ⟨k, c k⟩ ≠ 0 :=
  fun k => (Finset.prod_ne_zero_iff.mp hc) k (Finset.mem_univ k)
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
