-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_length_of_mem_support_fe70f044d187
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:34:32.8664+00:00
-- url     : https://prove2.me/submissions/e8d49c07-e439-4a91-92b3-46d1f78cece8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {σ : Type*} (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ}
    {t : ℕ} (hH : H.IsHomogeneous t) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) :
    (classList cls μ).length = t := by
  unfold classList
  rw [Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
  have h := hH (mem_support_iff.mp hμ)
  rw [Finsupp.weight_apply] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  exact h
end GroundTheory.Heights₂.Heights.NumbersDVR
