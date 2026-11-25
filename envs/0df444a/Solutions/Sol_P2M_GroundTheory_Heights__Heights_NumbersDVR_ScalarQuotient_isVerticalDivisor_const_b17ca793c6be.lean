-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_isVerticalDivisor_const_b17ca793c6be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:15:28.226306+00:00
-- url     : https://prove2.me/submissions/d14fc0c7-54f7-4ba3-bf6a-502c663f0ba0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PScalarQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_of_unit_off_special_da747d91115e


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
open GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [DecidableEq K]
omit [Fintype K] [∀ k, Fintype (ι k)] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
theorem _root_.solution (P : Ideal (MRing ι O)) [P.IsPrime] (ϖ : O) (u : Oˣ) (n : ℕ)
    (hP : (C ((u : O) * ϖ ^ n) : MRing ι O) ∉ P) :
    IsVerticalDivisor P ϖ 0 (C ((u : O) * ϖ ^ n)) 1 := by
  refine IsVerticalDivisor.of_unit_off_special
    ⟨0, 0, isWeightedHomogeneous_C _ _, isWeightedHomogeneous_one _ _, by funext k; simp⟩ hP
    (Ideal.IsPrime.ne_top' ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one)) ?_
  intro W hW _ _ hϖW
  refine ⟨1, C ((u : O) * ϖ ^ n), (Ideal.ne_top_iff_one W).mp hW.ne_top, ?_, ?_⟩
  · rw [map_mul, map_pow]
    intro h
    rcases hW.mem_or_mem h with h1 | h1
    · exact hW.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (u.isUnit.map C))
    · exact hϖW (hW.mem_of_pow_mem _ h1)
  · rw [one_mul, mul_one, sub_self]
    exact Submodule.zero_mem _
end GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
