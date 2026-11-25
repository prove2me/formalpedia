-- Prove2me | solution 1 for PositivityTheory.RgJS.NewtonIdentitiesAlt.bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:01.289611+00:00
-- url     : https://prove2.me/submissions/bf029f33-d187-49db-b7fc-40d1a6fb5997

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLowerBounds_NewtonIdentitiesLowDegree
import Theorems.Thm_PositivityTheory_RgJS_NewtonIdentitiesAlt_ev_zero
import Theorems.Thm_PositivityTheory_RgJS_NewtonIdentitiesAlt_newton
import Theorems.Thm_PositivityTheory_RgJS_NewtonIdentitiesAlt_card_filter_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.NewtonIdentitiesAlt
variable {A : Type} [Fintype A]
namespace PositivityTheory.RgJS.NewtonIdentitiesAlt
theorem _root_.solution [DecidableEq A] (a : A → ℂ) (N : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hp : ∀ k, 1 ≤ k → k ≤ N → ‖∑ i, a i ^ k‖ ≤ δ) : ∀ j, 1 ≤ j → j ≤ N → ‖ev a j‖ ≤ δ := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj1 hjN
  have hev : ∀ m, m < j → ‖ev a m‖ ≤ 1 := fun m hm => by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [ev_zero]
      simp
    · exact (ih m hm h (by omega)).trans hδ
  have hsum : ‖∑ x ∈ antidiagonal j with x.1 < j, (-1) ^ x.1 * ev a x.1 * ∑ i, a i ^ x.2‖ ≤ j * δ := by
    calc _ ≤ ∑ x ∈ antidiagonal j with x.1 < j, ‖(-1) ^ x.1 * ev a x.1 * ∑ i, a i ^ x.2‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ antidiagonal j with x.1 < j, δ := by
        apply Finset.sum_le_sum
        intro x hx
        simp only [Finset.mem_filter] at hx
        have e1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hx.1
        rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        calc ‖ev a x.1‖ * ‖∑ i, a i ^ x.2‖ ≤ 1 * δ :=
              mul_le_mul (hev _ hx.2) (hp _ (by omega) (by omega)) (norm_nonneg _) zero_le_one
          _ = δ := one_mul δ
      _ = (#{x ∈ antidiagonal j | x.1 < j} : ℝ) * δ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ j * δ := by
        gcongr
        exact_mod_cast card_filter_lt j
  have h2 : (j : ℝ) * ‖ev a j‖ ≤ j * δ := by
    have h3 := congrArg norm (newton a j)
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast] at h3
    rw [h3]
    exact hsum
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  exact le_of_mul_le_mul_left h2 hjpos
end PositivityTheory.RgJS.NewtonIdentitiesAlt
