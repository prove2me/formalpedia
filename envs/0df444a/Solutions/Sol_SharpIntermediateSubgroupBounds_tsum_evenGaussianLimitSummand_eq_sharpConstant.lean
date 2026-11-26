-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.tsum_evenGaussianLimitSummand_eq_sharpConstant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:56:28.727315+00:00
-- url     : https://prove2.me/submissions/bc9937dd-6561-4ceb-a6c4-c4ad386a236b

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_summable_nat_gaussian_inv_pow
import Theorems.Thm_SharpIntermediateSubgroupBounds_eulerC_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_gaussianTheta_eq_one_add_two_mul_tsum_pnat

section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
private theorem exp_neg_log_sq_nat_eq_inv_pow {p j : ℕ} (hp : 1 ≤ p) :
    Real.exp (-Real.log (p : ℝ) * (j : ℝ) ^ 2) =
      (p : ℝ)⁻¹ ^ (j * j) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  rw [show -Real.log (p : ℝ) * (j : ℝ) ^ 2 =
      (j * j : ℕ) * (-Real.log (p : ℝ)) by norm_num; ring]
  rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hpR]
end SharpIntermediateSubgroupBounds
end

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) :
    ∑' j : ℕ, evenGaussianLimitSummand p j = sharpConstant (p : ℝ) := by
  have hsum : Summable (fun j : ℕ ↦ evenGaussianLimitSummand p j) := by
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    refine ((summable_nat_gaussian_inv_pow hp).mul_left
      (2 * eulerC (p : ℝ))).of_nonneg_of_le ?_ ?_
    · intro j
      unfold evenGaussianLimitSummand centerMultiplicity
      split_ifs <;> positivity [eulerC_pos hpR]
    · intro j
      have hx : 0 ≤ eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j) :=
        mul_nonneg (eulerC_pos hpR).le (by positivity)
      unfold evenGaussianLimitSummand centerMultiplicity
      by_cases hj : j = 0
      · simp only [if_pos hj, Nat.cast_one, one_mul]
        linarith
      · rw [if_neg hj]
        change (2 : ℝ) * (eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j)) ≤
            2 * eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j)
        ring_nf
        exact le_rfl
  rw [hsum.tsum_eq_zero_add]
  have htheta : gaussianTheta (p : ℝ) =
      1 + 2 * ∑' j : ℕ, (p : ℝ)⁻¹ ^ ((j + 1) * (j + 1)) := by
    rw [gaussianTheta_eq_one_add_two_mul_tsum_pnat
      (by exact_mod_cast (by omega : 1 < p)),
      tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ ↦ Real.exp (-Real.log (p : ℝ) * (n : ℝ) ^ 2))]
    congr 2
    apply tsum_congr
    intro j
    simpa using exp_neg_log_sq_nat_eq_inv_pow (p := p) (j := j + 1) (by omega)
  rw [sharpConstant, htheta]
  simp only [evenGaussianLimitSummand, centerMultiplicity, if_pos, Nat.cast_one,
    one_mul, if_neg (Nat.succ_ne_zero _), Nat.cast_ofNat]
  rw [tsum_mul_left, tsum_mul_left]
  simp
  ring
end SharpIntermediateSubgroupBounds
