-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.frameProd_diagonal_cast_real_eq_gammaR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:05.013826+00:00
-- url     : https://prove2.me/submissions/f34b3148-2632-479e-9a77-78bcd16ff44b

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_qWeight_succ
import Theorems.Thm_SharpIntermediateSubgroupBounds_qFactorial_cast_real_eq_pow_mul_gammaR
import Theorems.Thm_SharpIntermediateSubgroupBounds_framePower_succ
import Theorems.Thm_SharpIntermediateSubgroupBounds_frameProd_mul_qFactorial

section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
private theorem frameWeight_succ (r : ℕ) :
    frameWeight (r + 1) = frameWeight r + r := by
  simp [frameWeight, Finset.sum_range_succ]
private theorem frameWeight_add_qWeight (r : ℕ) :
    frameWeight r + qWeight r = r * r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [frameWeight_succ, qWeight_succ]
      calc
        frameWeight r + r + (qWeight r + (r + 1)) =
            (frameWeight r + qWeight r) + (2 * r + 1) := by ring
        _ = r * r + (2 * r + 1) := by rw [ih]
        _ = (r + 1) * (r + 1) := by ring
private theorem framePower_cast_real {p r : ℕ} :
    (framePower p r : ℝ) = (p : ℝ) ^ frameWeight r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [framePower_succ, Nat.cast_mul, Nat.cast_pow, ih, frameWeight_succ, pow_add]
end SharpIntermediateSubgroupBounds
end

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p r : ℕ} (hp : 2 ≤ p) :
    (frameProd p r r : ℝ) =
      (p : ℝ) ^ (r * r) * gammaR (p : ℝ) r := by
  have hdiag := frameProd_mul_qFactorial (q := p) (n := r) (k := r) (le_refl r)
  simp only [Nat.sub_self, qFactorial_zero, mul_one] at hdiag
  have hreal : (frameProd p r r : ℝ) =
      (framePower p r : ℝ) * (qFactorial p r : ℝ) := by exact_mod_cast hdiag
  rw [hreal, framePower_cast_real,
    qFactorial_cast_real_eq_pow_mul_gammaR (by omega), ← mul_assoc,
    ← pow_add, frameWeight_add_qWeight]
end SharpIntermediateSubgroupBounds
