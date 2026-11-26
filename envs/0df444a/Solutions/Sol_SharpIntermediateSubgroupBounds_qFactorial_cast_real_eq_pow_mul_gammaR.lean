-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.qFactorial_cast_real_eq_pow_mul_gammaR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:58.332794+00:00
-- url     : https://prove2.me/submissions/69acb385-a213-4a88-ab47-e499f1614fa2

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_succ
import Theorems.Thm_SharpIntermediateSubgroupBounds_qWeight_succ
import Theorems.Thm_SharpIntermediateSubgroupBounds_qFactorial_succ

section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
private theorem cast_qpow_sub_one_factor {q m : ℕ} (hq : 1 ≤ q) :
    ((q ^ (m + 1) - 1 : ℕ) : ℝ) =
      (q : ℝ) ^ (m + 1) * (1 - (q : ℝ)⁻¹ ^ (m + 1)) := by
  have hpow : 1 ≤ q ^ (m + 1) := one_le_pow₀ hq
  rw [Nat.cast_sub hpow, Nat.cast_one, Nat.cast_pow]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [inv_pow]
  field_simp
end SharpIntermediateSubgroupBounds
end

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {q r : ℕ} (hq : 1 ≤ q) :
    (qFactorial q r : ℝ) = (q : ℝ) ^ qWeight r * gammaR (q : ℝ) r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [qFactorial_succ, Nat.cast_mul, ih, qWeight_succ, gammaR_succ,
        cast_qpow_sub_one_factor hq, pow_add]
      ring
end SharpIntermediateSubgroupBounds
