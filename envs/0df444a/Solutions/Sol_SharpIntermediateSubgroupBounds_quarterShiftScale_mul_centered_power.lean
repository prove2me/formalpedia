-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.quarterShiftScale_mul_centered_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:29.171581+00:00
-- url     : https://prove2.me/submissions/70256754-7a51-40df-afd5-b1d10500a35b

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
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
theorem _root_.solution {p a : ℕ} (hp : 2 ≤ p) :
    quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) =
      Real.rpow (p : ℝ) (-(((2 * a + 1 : ℕ) : ℝ) ^ 2 / 4)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  change quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) =
    (p : ℝ) ^ (-(((2 * a + 1 : ℕ) : ℝ) ^ 2 / 4))
  rw [Real.rpow_def_of_pos hpR]
  rw [← exp_neg_log_nat_eq_inv_pow (p := p) (m := a * (a + 1)) (by omega),
    quarterShiftScale, ← Real.exp_add]
  congr 1
  push_cast
  ring
end SharpIntermediateSubgroupBounds
