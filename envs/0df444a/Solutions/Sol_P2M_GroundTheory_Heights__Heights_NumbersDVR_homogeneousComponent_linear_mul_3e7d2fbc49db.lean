-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_homogeneousComponent_linear_mul_3e7d2fbc49db
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:02.124465+00:00
-- url     : https://prove2.me/submissions/74940292-212e-4b7a-9d70-990eeec05666

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {σ : Type*} {L : MvPolynomial σ ℤ} (hL : L.IsHomogeneous 1)
    (P : MvPolynomial σ ℤ) (t : ℕ) :
    homogeneousComponent t (L * P) = if t = 0 then 0 else L * homogeneousComponent (t - 1) P := by
  conv_lhs => rw [← sum_homogeneousComponent P, Finset.mul_sum, map_sum]
  have h : ∀ j, homogeneousComponent t (L * homogeneousComponent j P) =
      if j = t - 1 ∧ t ≠ 0 then L * homogeneousComponent j P else 0 := by
    intro j
    have hm := hL.mul (homogeneousComponent_isHomogeneous j P)
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hm)]
    by_cases hjt : j = t - 1 ∧ t ≠ 0
    · rw [if_pos (by omega), if_pos hjt]
    · rw [if_neg (by omega), if_neg hjt]
  simp only [h]
  by_cases ht : t = 0
  · simp [ht]
  · simp only [ht, ne_eq, not_false_eq_true, and_true, if_false]
    rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · rw [homogeneousComponent_eq_zero, mul_zero]
      rw [Finset.mem_range] at hmem
      omega
end GroundTheory.Heights₂.Heights.NumbersDVR
