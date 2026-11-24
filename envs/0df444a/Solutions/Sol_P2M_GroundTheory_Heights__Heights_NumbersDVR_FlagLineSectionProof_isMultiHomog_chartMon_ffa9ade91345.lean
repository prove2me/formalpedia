-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_isMultiHomog_chartMon_ffa9ade91345
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:18.103179+00:00
-- url     : https://prove2.me/submissions/84071564-0e90-4f9c-b6b1-37a70d102318

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
theorem _root_.solution (c : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (chartMon F M c α) (liftN α) := by
  unfold IsMultiHomog chartMon
  have h := IsWeightedHomogeneous.prod (w := blockWeight (bundleIdx ι M)) Finset.univ
    (fun k => (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ^ α k)
    (fun k => α k • blockWeight (bundleIdx ι M) ⟨some k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X F _ _).pow (α k))
  convert h using 1
  funext o
  cases o with
  | none => simp [liftN, blockWeight, Finset.sum_apply]
  | some k => simp [liftN, blockWeight, Finset.sum_apply, Pi.single_apply]
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
