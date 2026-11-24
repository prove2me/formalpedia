-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_multiHomog_25f3cafc54d6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:13.888185+00:00
-- url     : https://prove2.me/submissions/403fd95e-6517-4fda-bf22-9eef88e07adc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PColonMultiHomog

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {R : Type*} [CommRing R] {K : Type} [DecidableEq K]
    {ι : K → Type} (y f : MRing ι R) (b s : K → ℕ) (hf : IsMultiHomog f s) :
    weightedHomogeneousComponent (blockWeight ι) b y * f =
      weightedHomogeneousComponent (blockWeight ι) (b + s) (y * f) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hx1
    · rfl
    · by_cases h2 : coeff x.2 f = 0
      · rw [h2, mul_zero, mul_zero]
      · exfalso
        apply hx1
        have hw := hf h2
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [← hx, map_add, hw] at hd
        exact add_right_cancel hd
  · refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hx1
    · by_cases h2 : coeff x.2 f = 0
      · rw [h2, mul_zero]
      · exfalso
        apply hd
        have hw := hf h2
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [← hx, map_add, hw, hx1]
    · rw [zero_mul]
end GroundTheory.Heights₂.Heights.NumbersDVR
