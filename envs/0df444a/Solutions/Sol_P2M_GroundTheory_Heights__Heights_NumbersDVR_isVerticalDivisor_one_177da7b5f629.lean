-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_one_177da7b5f629
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:40.562842+00:00
-- url     : https://prove2.me/submissions/02cd3f70-b0b4-41da-9bcc-66a7be07a413

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_one_e110294ad3db


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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type*} [DecidableEq K] {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (H : Ideal (MRing ι O)) [H.IsPrime] :
    IsVerticalDivisor H ϖ 0 1 1 where
  degrees := ⟨0, 0, isWeightedHomogeneous_one _ _, isWeightedHomogeneous_one _ _, by
    funext k; simp⟩
  num_not_mem := Ideal.IsPrime.ne_top' ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one)
  den_not_mem := Ideal.IsPrime.ne_top' ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one)
  vertical := by
    intro W hW
    simp [ratDiv, divCycle_one] at hW
  unit_off_special := by
    intro W hW _ _ _
    refine ⟨1, 1, ?_, ?_, ?_⟩
    · exact (Ideal.ne_top_iff_one W).mp hW.ne_top
    · exact (Ideal.ne_top_iff_one W).mp hW.ne_top
    · simp
end GroundTheory.Heights₂.Heights.NumbersDVR
