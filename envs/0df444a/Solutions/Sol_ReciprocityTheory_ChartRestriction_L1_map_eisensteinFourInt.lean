-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.map_eisensteinFourInt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:49.289311+00:00
-- url     : https://prove2.me/submissions/d2d462a6-30de-4ac8-9de8-b5389bcc8a45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1
private theorem hasSum_sigma_mul_qParam_pow_modularForm_E {k : ℕ} (hk : 3 ≤ k) (hke : Even k) (C : ℂ)
    (hC : (riemannZeta k)⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ k / ((k - 1).factorial : ℂ) = C)
    (τ : ℍ) :
    HasSum (fun m : ℕ => (if m = 0 then (1 : ℂ) else C * (ArithmeticFunction.sigma (k - 1) m : ℂ)) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.E hk τ) := by
  set q := Function.Periodic.qParam 1 (τ : ℂ) with hqdef
  have hqe : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) = q := by
    simp [hqdef, Function.Periodic.qParam]
  have hq : ‖q‖ < 1 := by
    rw [hqdef, Function.Periodic.norm_qParam]
    refine (Real.exp_lt_exp.mpr ?_).trans_eq Real.exp_zero
    have := τ.im_pos
    have := Real.pi_pos
    simp only [UpperHalfPlane.coe_im, div_one]
    nlinarith
  have hσ : ∀ n : ℕ, ‖((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n‖ ≤ (n : ℝ) ^ k * ‖q‖ ^ n := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    gcongr
    rw [ArithmeticFunction.sigma_apply]
    push_cast
    calc ∑ d ∈ n.divisors, (d : ℝ) ^ (k - 1) ≤ ∑ d ∈ n.divisors, (n : ℝ) ^ (k - 1) :=
          Finset.sum_le_sum fun d hd => pow_le_pow_left₀ (by positivity)
            (by exact_mod_cast Nat.divisor_le hd) _
      _ = (n.divisors.card : ℝ) * (n : ℝ) ^ (k - 1) := by simp
      _ ≤ (n : ℝ) * (n : ℝ) ^ (k - 1) := by
          gcongr
          exact_mod_cast Nat.card_divisors_le_self n
      _ = (n : ℝ) ^ k := by
          rw [← pow_succ']
          congr 1
          omega
  have hsum : Summable fun n : ℕ => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n :=
    Summable.of_norm_bounded (summable_pow_mul_geometric_of_norm_lt_one k (by simpa using hq)) hσ
  have hsum1 : Summable fun n : ℕ =>
      ((ArithmeticFunction.sigma (k - 1) (n + 1) : ℕ) : ℂ) * q ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hsum
  have hE := EisensteinSeries.q_expansion_riemannZeta hk hke τ
  rw [hE, hC, hqe]
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, if_true, mul_one,
    add_sub_cancel_left, Nat.add_eq_zero, one_ne_zero, and_false, if_false]
  have ht : ∑' n : ℕ+, ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ (n : ℕ) =
      ∑' n : ℕ, ((ArithmeticFunction.sigma (k - 1) (n + 1) : ℕ) : ℂ) * q ^ (n + 1) :=
    tsum_pnat_eq_tsum_succ (f := fun n => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n)
  convert hsum1.hasSum.mul_left C using 1 <;>
    first
    | rfl
    | (funext n <;> ring)
    | (congr 1 <;> (rw [← ht]; apply tsum_congr; intro n; simp))
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : e4Z.map (Int.castRingHom ℂ) = qExpansion 1 E₄ := by
  have hE : E₄ = ModularForm.E (k := 4) (by norm_num) := rfl
  ext m
  refine ModularFormClass.qExpansion_coeff_unique (f := E₄) (h := 1)
    (c := fun m => PowerSeries.coeff m (e4Z.map (Int.castRingHom ℂ))) one_pos (by simp) ?_ m
  intro τ
  have hC : (riemannZeta ((4 : ℕ) : ℂ))⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ 4 /
      (((4 - 1).factorial : ℕ) : ℂ) = 240 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
    have hI : Complex.I ^ 4 = 1 := Complex.I_pow_four
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    field_simp
    ring_nf
    rw [hI]
    ring
  have h := hasSum_sigma_mul_qParam_pow_modularForm_E (k := 4) (by norm_num) (by decide) 240 hC τ
  rw [hE]
  convert h using 2 with n
  simp only [e4Z, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.L1
