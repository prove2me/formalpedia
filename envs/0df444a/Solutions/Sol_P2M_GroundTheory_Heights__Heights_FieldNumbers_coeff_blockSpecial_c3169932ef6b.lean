-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_blockSpecial_c3169932ef6b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:20:53.804107+00:00
-- url     : https://prove2.me/submissions/0c414879-5878-47d8-8dc4-0f69be9f39e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsValuativeCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartDehomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PValuativeCentre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_blockSpecial_monomial_ab1e8c92d616

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
  {κ : Type*} [CommRing κ]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (ρ : MRing ι F →+* κ) (f : MRing ι F) (e : K →₀ ℕ) :
    coeff e (blockSpecial ρ f) = ρ (weightedHomogeneousComponent (blockWeight ι) (⇑e) f) := by
  classical
  conv_lhs => rw [f.as_sum]
  rw [weightedHomogeneousComponent_apply, map_sum, coeff_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [blockSpecial_monomial, coeff_C_mul, coeff_monomial]
  have hiff : Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d) = e ↔
      Finsupp.weight (blockWeight ι) d = ⇑e := by
    rw [Equiv.symm_apply_eq]; rfl
  by_cases h : Finsupp.weight (blockWeight ι) d = ⇑e
  · rw [if_pos (hiff.mpr h), if_pos h, mul_one]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]
end GroundTheory.Heights₂.Heights.FieldNumbers
