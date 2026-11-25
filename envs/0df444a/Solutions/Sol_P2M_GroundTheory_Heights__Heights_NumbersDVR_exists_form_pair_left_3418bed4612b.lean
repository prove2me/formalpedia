-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_pair_left_3418bed4612b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:14.421742+00:00
-- url     : https://prove2.me/submissions/da4330e6-da90-4887-b1da-814769965a31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialDimBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVertCutEff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_component_not_mem_53dbbac47368
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_mul_form_f630f1747419


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
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P H : Ideal (MRing ι R)} [hP : P.IsPrime]
    (hPm : IsMultiHomogIdeal P) (hPH : P ≤ H) {f g u v : MRing ι R} {bf bg : K → ℕ}
    (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg) (hfP : f ∉ P) (hu : u ∉ H)
    (h : u * f - v * g ∈ P) :
    ∃ (u' v' : MRing ι R) (e d : K → ℕ), IsMultiHomog u' e ∧ IsMultiHomog v' d ∧
      d + bg = e + bf ∧ u' ∉ H ∧ u' * f - v' * g ∈ P := by
  classical
  obtain ⟨e, he⟩ := exists_component_not_mem hu
  set u' := weightedHomogeneousComponent (blockWeight ι) e u with hu'
  have hc := hPm _ h (e + bf)
  rw [map_sub, weightedHomogeneousComponent_mul_form hf, weightedHomogeneousComponent_mul_form hg,
    if_pos le_add_self, add_tsub_cancel_right, ← hu'] at hc
  by_cases hle : bg ≤ e + bf
  · rw [if_pos hle] at hc
    exact ⟨u', _, e, e + bf - bg, weightedHomogeneousComponent_isWeightedHomogeneous _ _,
      weightedHomogeneousComponent_isWeightedHomogeneous _ _, tsub_add_cancel_of_le hle, he, hc⟩
  · rw [if_neg hle, sub_zero] at hc
    exact ((hP.mem_or_mem hc).elim (fun h' => he (hPH h')) hfP).elim
end GroundTheory.Heights₂.Heights.NumbersDVR
