-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_of_unit_off_special_da747d91115e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:11:26.813301+00:00
-- url     : https://prove2.me/submissions/a6a538b4-3bd3-4812-887c-40c40bfccb0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_mul_sub_mem_0d8c554dd825
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6

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
open MvPolynomial
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace IsVerticalDivisor
theorem _root_.solution {P : Ideal (MRing ι O)} {ϖ : O} {b : K → ℤ}
    {f g : MRing ι O}
    (degrees : ∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
      (fun k => (bf k : ℤ) - bg k) = b)
    (hf : f ∉ P) (hg : g ∉ P)
    (hunit : ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W →
      (C ϖ : MRing ι O) ∉ W → ∃ u v : MRing ι O, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P) :
    IsVerticalDivisor P ϖ b f g where
  degrees := degrees
  num_not_mem := hf
  den_not_mem := hg
  unit_off_special := hunit
  vertical := by
    intro W hW
    by_contra hϖ
    have hsupp : W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
      by_cases h1 : divCycle P f W = 0
      · have h2 : divCycle P g W ≠ 0 := by
          intro h2; apply hW; unfold ratDiv; rw [h1, h2, sub_zero]
        exact le_and_isRelevant_of_divCycle_ne_zero h2
      · exact le_and_isRelevant_of_divCycle_ne_zero h1
    obtain ⟨u, v, hu, hv, h⟩ := hunit W hsupp.1 hsupp.2.1 hsupp.2.2 hϖ
    apply hW
    unfold ratDiv
    rw [divCycle_eq_of_mul_sub_mem hu hv h, sub_self]
end IsVerticalDivisor
end GroundTheory.Heights₂.Heights.NumbersDVR
