-- Prove2me | solution 1 for P2M_GlobalTheory_deriv_inv_Gamma__ne_zero_e95e241ec1cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:43:51.122536+00:00
-- url     : https://prove2.me/submissions/13ae798b-a26c-4ded-838a-4e9c3bde1891

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Theorems.Thm_P2M_GlobalTheory_inv_Gamma__eq_mul_inv_add_two_9fd1e0e03194
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
namespace GlobalTheory
private lemma deriv_inv_Gammaℝ_eq_shift (x : ℂ) :
    deriv (fun s : ℂ => (Gammaℝ s)⁻¹) x =
      1 / (2 * Real.pi) * (Gammaℝ (x + 2))⁻¹ +
        x / (2 * Real.pi) * deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (x + 2) := by
  have hF : (fun s : ℂ => (Gammaℝ s)⁻¹) = fun s => s / (2 * Real.pi) * (Gammaℝ (s + 2))⁻¹ :=
    funext inv_Gammaℝ_eq_mul_inv_add_two
  have h1 : HasDerivAt (fun s : ℂ => s / (2 * (Real.pi : ℂ))) (1 / (2 * Real.pi)) x :=
    (hasDerivAt_id' x).div_const _
  have h2 : HasDerivAt (fun s : ℂ => (Gammaℝ (s + 2))⁻¹)
      (deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (x + 2)) x :=
    HasDerivAt.comp_add_const x 2 (differentiable_Gammaℝ_inv (x + 2)).hasDerivAt
  conv_lhs => rw [hF]
  exact (h1.mul h2).deriv
end GlobalTheory
end

set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n : ℕ) :
    deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (-(2 * n)) ≠ 0 := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  induction n with
  | zero =>
    rw [deriv_inv_Gammaℝ_eq_shift]
    have h2 : Gammaℝ 2 ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num)
    simp [h2, Real.pi_ne_zero]
  | succ n ih =>
    rw [deriv_inv_Gammaℝ_eq_shift]
    have e : (-(2 * ((n + 1 : ℕ) : ℂ))) + 2 = -(2 * (n : ℂ)) := by push_cast; ring
    rw [e, inv_eq_zero.mpr (Gammaℝ_eq_zero_iff.mpr ⟨n, rfl⟩), mul_zero, zero_add]
    refine mul_ne_zero (div_ne_zero ?_ hπ) ih
    have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    push_cast
    exact neg_ne_zero.mpr (mul_ne_zero two_ne_zero this)
end GlobalTheory
