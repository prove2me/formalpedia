-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_homogeneousComponent_mul_of_isHomogeneous_7d8e3d96fdd1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:28.194168+00:00
-- url     : https://prove2.me/submissions/ac7d159e-db8c-4903-b301-274822982e0d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {σ : Type*} [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.AntisymDivisible
theorem _root_.solution {Δ : MvPolynomial σ ℝ} {D : ℕ}
    (hΔ : Δ.IsHomogeneous D) (l : MvPolynomial σ ℝ) (n : ℕ) :
    homogeneousComponent (D + n) (Δ * l) = Δ * homogeneousComponent n l := by
  conv_lhs => rw [← sum_homogeneousComponent l]
  rw [Finset.mul_sum, map_sum]
  have key : ∀ m, homogeneousComponent (D + n) (Δ * homogeneousComponent m l) =
      if n = m then Δ * homogeneousComponent n l else 0 := by
    intro m
    rw [homogeneousComponent_of_mem (hΔ.mul (homogeneousComponent_isHomogeneous m l))]
    by_cases h : n = m
    · subst h; simp
    · rw [if_neg (by omega), if_neg h]
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero, mul_zero]
    simp only [Finset.mem_range, not_lt] at h
    omega
end GroundTheory.Heights₂.Heights.AntisymDivisible
