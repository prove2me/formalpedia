-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.no_subquarter_rpow_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:51.191425+00:00
-- url     : https://prove2.me/submissions/f655aa0e-75ad-4cc7-9ab5-5b3c32457d18

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_no_subquarter_normalized_exponential_bound
section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
private theorem exp_neg_log_nat_eq_inv_pow {p m : ℕ} (hp : 1 ≤ p) :
    Real.exp (-Real.log (p : ℝ) * (m : ℝ)) = (p : ℝ)⁻¹ ^ m := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  rw [show -Real.log (p : ℝ) * (m : ℝ) =
      (m : ℕ) * (-Real.log (p : ℝ)) by norm_num; ring]
  rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hpR]
end SharpIntermediateSubgroupBounds
end

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {α C : ℝ}
    (hα : α < 1 / 4) :
    ¬ ∀ a : ℕ,
      (totalQBinom p (2 * a) : ℝ) ≤
        C * Real.rpow (p : ℝ) (4 * α * (a : ℝ) ^ 2) := by
  intro hbound
  apply no_subquarter_normalized_exponential_bound hp hα
  intro a
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  calc
    (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ) ≤
        (p : ℝ)⁻¹ ^ (a * a) *
          (C * Real.rpow (p : ℝ) (4 * α * (a : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hbound a) (by positivity)
    _ = C * Real.exp
          (Real.log (p : ℝ) * (4 * α - 1) * (a : ℝ) ^ 2) := by
      change (p : ℝ)⁻¹ ^ (a * a) *
          (C * (p : ℝ) ^ (4 * α * (a : ℝ) ^ 2)) =
        C * Real.exp
          (Real.log (p : ℝ) * (4 * α - 1) * (a : ℝ) ^ 2)
      rw [Real.rpow_def_of_pos hpR]
      rw [← exp_neg_log_nat_eq_inv_pow (p := p) (m := a * a) (by omega)]
      calc
        Real.exp (-Real.log (p : ℝ) * ((a * a : ℕ) : ℝ)) *
              (C * Real.exp (Real.log (p : ℝ) *
                (4 * α * (a : ℝ) ^ 2))) =
            C * (Real.exp (-Real.log (p : ℝ) * ((a * a : ℕ) : ℝ)) *
              Real.exp (Real.log (p : ℝ) * (4 * α * (a : ℝ) ^ 2))) := by ring
        _ = C * Real.exp
            ((-Real.log (p : ℝ) * ((a * a : ℕ) : ℝ)) +
              Real.log (p : ℝ) * (4 * α * (a : ℝ) ^ 2)) := by
          rw [Real.exp_add]
        _ = C * Real.exp
            (Real.log (p : ℝ) * (4 * α - 1) * (a : ℝ) ^ 2) := by
          congr 2
          push_cast
          ring
end SharpIntermediateSubgroupBounds
