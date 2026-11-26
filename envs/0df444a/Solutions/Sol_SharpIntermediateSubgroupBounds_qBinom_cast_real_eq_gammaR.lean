-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.qBinom_cast_real_eq_gammaR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:02.28915+00:00
-- url     : https://prove2.me/submissions/6b766297-2cb3-48e0-b115-66ae49639157

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_qWeight_split
import Theorems.Thm_SharpIntermediateSubgroupBounds_qFactorial_cast_real_eq_pow_mul_gammaR
import Theorems.Thm_SharpIntermediateSubgroupBounds_qBinom_mul_qFactorials


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {q n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    (qBinom q n k : ℝ) =
      (q : ℝ) ^ (k * (n - k)) * gammaR (q : ℝ) n /
        (gammaR (q : ℝ) k * gammaR (q : ℝ) (n - k)) := by
  have hnat := qBinom_mul_qFactorials hq hk
  have hreal : (qBinom q n k : ℝ) * (qFactorial q k : ℝ) *
      (qFactorial q (n - k) : ℝ) = (qFactorial q n : ℝ) := by
    exact_mod_cast hnat
  rw [qFactorial_cast_real_eq_pow_mul_gammaR (by omega),
    qFactorial_cast_real_eq_pow_mul_gammaR (by omega),
    qFactorial_cast_real_eq_pow_mul_gammaR (by omega)] at hreal
  have hsplit := qWeight_split hk
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hpow : (q : ℝ) ^ qWeight n =
      ((q : ℝ) ^ qWeight k * (q : ℝ) ^ qWeight (n - k)) *
        (q : ℝ) ^ (k * (n - k)) := by
    rw [hsplit, pow_add, pow_add]
  have hden : gammaR (q : ℝ) k * gammaR (q : ℝ) (n - k) ≠ 0 :=
    mul_ne_zero (ne_of_gt (gammaR_pos (by exact_mod_cast (by omega : 1 < q)) k))
      (ne_of_gt (gammaR_pos (by exact_mod_cast (by omega : 1 < q)) (n - k)))
  apply (eq_div_iff hden).2
  have hpowers : (q : ℝ) ^ qWeight k * (q : ℝ) ^ qWeight (n - k) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hq0) (pow_ne_zero _ hq0)
  apply mul_left_cancel₀ hpowers
  calc
    ((q : ℝ) ^ qWeight k * (q : ℝ) ^ qWeight (n - k)) *
          ((qBinom q n k : ℝ) *
            (gammaR (q : ℝ) k * gammaR (q : ℝ) (n - k))) =
        (qBinom q n k : ℝ) *
          ((q : ℝ) ^ qWeight k * gammaR (q : ℝ) k) *
          ((q : ℝ) ^ qWeight (n - k) * gammaR (q : ℝ) (n - k)) := by ring
    _ = (q : ℝ) ^ qWeight n * gammaR (q : ℝ) n := hreal
    _ = ((q : ℝ) ^ qWeight k * (q : ℝ) ^ qWeight (n - k)) *
          ((q : ℝ) ^ (k * (n - k)) * gammaR (q : ℝ) n) := by
      rw [hpow]
      ring
end SharpIntermediateSubgroupBounds
