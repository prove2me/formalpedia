-- Prove2me | solution 1 for PermanentRollout.affine_tendsto_shifted_choose_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/8e816943-e760-4bb1-b76a-8f3f65a6ef8d

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    (n M₀ : ℕ) :
    Tendsto
      (fun m : ℕ =>
        ((m + M₀ + n).choose n : ℝ) /
          ((m + n).choose n : ℝ))
      atTop (𝓝 1) := by
  have hnum :
      (fun m : ℕ => ((m + M₀ + n).choose n : ℝ)) ~[atTop]
        (fun m : ℕ =>
          ((m + M₀ + n : ℕ) : ℝ) ^ n / (n.factorial : ℝ)) := by
    simpa [Function.comp_def, Nat.add_assoc] using
      (isEquivalent_choose n).comp_tendsto
        (tendsto_add_atTop_nat (M₀ + n))
  have hden :
      (fun m : ℕ => ((m + n).choose n : ℝ)) ~[atTop]
        (fun m : ℕ =>
          ((m + n : ℕ) : ℝ) ^ n / (n.factorial : ℝ)) := by
    simpa [Function.comp_def] using
      (isEquivalent_choose n).comp_tendsto
        (tendsto_add_atTop_nat n)
  have hbase :
      Tendsto
        (fun m : ℕ =>
          (((M₀ + n : ℕ) : ℝ) + 1 * (m : ℝ)) /
            (((n : ℕ) : ℝ) + 1 * (m : ℝ)))
        atTop (𝓝 (1 : ℝ)) := by
    simpa using
      (tendsto_add_mul_div_add_mul_atTop_nhds
        (((M₀ + n : ℕ) : ℝ)) (((n : ℕ) : ℝ))
        (1 : ℝ) (one_ne_zero : (1 : ℝ) ≠ 0))
  have hpow :
      Tendsto
        (fun m : ℕ =>
          ((m + M₀ + n : ℕ) : ℝ) ^ n /
            ((m + n : ℕ) : ℝ) ^ n)
        atTop (𝓝 (1 : ℝ)) := by
    convert hbase.pow n using 1
    · ext m
      simp [div_pow, Nat.cast_add, add_comm, add_assoc]
    · simp
  have hfact : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast n.factorial_ne_zero
  have hequiv :
      (fun m : ℕ =>
        ((m + M₀ + n).choose n : ℝ) /
          ((m + n).choose n : ℝ)) ~[atTop]
        (fun m : ℕ =>
          ((m + M₀ + n : ℕ) : ℝ) ^ n /
            ((m + n : ℕ) : ℝ) ^ n) := by
    convert hnum.div hden using 1
    · rfl
    · ext m
      dsimp
      field_simp
  exact hequiv.symm.tendsto_nhds hpow
end PermanentRollout
