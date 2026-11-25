-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__isMultiHomog_6dc8a1e2712d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:22.322578+00:00
-- url     : https://prove2.me/submissions/2f0af794-a6f9-4ca1-9755-f68043953818

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools

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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleChartSection
open FlagBundleSectionForms (chartPow chartMono liftNat)
variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleChartSection
theorem _root_.solution (g : (Σ o, bundleIdx ι M o) → MRing (bundleIdx ι M) F) (e : Option K → ℕ)
    (hs : ∀ k (p : ι k), g ⟨some k, p⟩ = X ⟨some k, p⟩) (hn : ∀ l, IsMultiHomog (g ⟨none, l⟩) e)
    {q : MRing (bundleIdx ι M) F} {d : Option K → ℕ} (hq : IsMultiHomog q d) :
    IsMultiHomog (bind₁ g q) (substDeg e d) := by
  let Λ : (Option K → ℕ) →+ (Option K → ℕ) :=
    { toFun := substDeg e
      map_zero' := by funext o; cases o <;> simp [substDeg]
      map_add' := fun d d' => by funext o; cases o <;> simp [substDeg] <;> ring }
  have hg : ∀ v, IsWeightedHomogeneous (blockWeight (bundleIdx ι M)) (g v) (Λ (blockWeight _ v)) := by
    rintro ⟨_ | k, p⟩
    · have : Λ (blockWeight (bundleIdx ι M) ⟨none, p⟩) = e := by
        funext o; cases o <;> simp [Λ, substDeg, blockWeight]
      rw [this]
      exact hn p
    · have : Λ (blockWeight (bundleIdx ι M) ⟨some k, p⟩) = blockWeight (bundleIdx ι M) ⟨some k, p⟩ := by
        funext o; cases o <;> simp [Λ, substDeg, blockWeight, Pi.single_apply]
      rw [this, show g ⟨some k, p⟩ = X ⟨some k, p⟩ from hs k p]
      exact isWeightedHomogeneous_X F _ _
  rw [← q.support_sum_monomial_coeff, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  have hmd : Finsupp.weight (blockWeight (bundleIdx ι M)) m = d := hq (mem_support_iff.mp hm)
  rw [bind₁_monomial]
  have := (isWeightedHomogeneous_C (blockWeight (bundleIdx ι M)) (coeff m q)).mul
    (IsWeightedHomogeneous.prod m.support (fun v => g v ^ m v) (fun v => m v • Λ (blockWeight _ v))
      (fun v _ => (hg v).pow (m v)))
  rw [zero_add] at this
  have hΛ : substDeg e d = ∑ v ∈ m.support, m v • Λ (blockWeight (bundleIdx ι M) v) := by
    show Λ d = _
    rw [← hmd, Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp only [map_nsmul]
  rw [hΛ]
  exact this
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleChartSection
