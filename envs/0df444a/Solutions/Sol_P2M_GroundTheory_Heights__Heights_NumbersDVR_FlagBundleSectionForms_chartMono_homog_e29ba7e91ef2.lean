-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartMono_homog_e29ba7e91ef2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:22.297612+00:00
-- url     : https://prove2.me/submissions/2ceff1f0-3a40-477d-b610-7544320b6f1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools

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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionForms
variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionForms
theorem _root_.solution (M : ℕ) (c : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (chartMono (F := F) M c α) (liftNat α) := by
  have h := IsWeightedHomogeneous.prod (R := F) Finset.univ
    (fun k => X (⟨some k, c k⟩ : Σ o, bundleIdx ι M o) ^ α k)
    (fun k => α k • blockWeight (bundleIdx ι M) ⟨some k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X F _ _).pow (α k))
  have hw : liftNat α = ∑ k, α k • blockWeight (bundleIdx ι M) ⟨some k, c k⟩ := by
    funext o
    cases o with
    | none => simp [liftNat, blockWeight, Finset.sum_apply, Pi.single_apply]
    | some k => simp [liftNat, blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [IsMultiHomog, chartMono, hw]
  exact h
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionForms
