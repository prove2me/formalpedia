-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.multipliable_euler_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:53:57.87379+00:00
-- url     : https://prove2.me/submissions/87f83fd0-f40c-42d8-9ea9-32f18a40923d

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Theorems.Thm_SharpIntermediateSubgroupBounds_summable_eulerCorrection
section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
private lemma euler_factor_eq_one_add (p : ℝ) (n : ℕ)
    (h : 1 - p⁻¹ ^ (n + 1) ≠ 0) :
    (1 - p⁻¹ ^ (n + 1))⁻¹ = 1 + eulerCorrection p n := by
  simp only [eulerCorrection, div_eq_mul_inv]
  calc
    (1 - p⁻¹ ^ (n + 1))⁻¹ =
        ((1 - p⁻¹ ^ (n + 1)) + p⁻¹ ^ (n + 1)) *
          (1 - p⁻¹ ^ (n + 1))⁻¹ := by rw [sub_add_cancel, one_mul]
    _ = 1 + p⁻¹ ^ (n + 1) * (1 - p⁻¹ ^ (n + 1))⁻¹ := by
      rw [add_mul, mul_inv_cancel₀ h]
private lemma eulerCorrection_nonneg {p : ℝ} (hp : 2 ≤ p) (n : ℕ) :
    0 ≤ eulerCorrection p n := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ p⁻¹ := (inv_pos.mpr hp0).le
  have hq_half : p⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
  have ht0 : 0 ≤ p⁻¹ ^ (n + 1) := pow_nonneg hq0 _
  have ht_half : p⁻¹ ^ (n + 1) ≤ (2 : ℝ)⁻¹ := by
    calc
      p⁻¹ ^ (n + 1) ≤ p⁻¹ ^ 1 :=
        pow_le_pow_of_le_one hq0 (hq_half.trans (by norm_num)) (by omega)
      _ ≤ (2 : ℝ)⁻¹ := by simpa using hq_half
  exact div_nonneg ht0 (by linarith)
end SharpIntermediateSubgroupBounds
end

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℝ} (hp : 2 ≤ p) :
    Multipliable (fun n : ℕ ↦ (1 - p⁻¹ ^ (n + 1))⁻¹) := by
  have hs := summable_eulerCorrection hp
  have habs (n : ℕ) : |eulerCorrection p n| = eulerCorrection p n :=
    abs_of_nonneg (eulerCorrection_nonneg hp n)
  have hm : Multipliable (fun n : ℕ ↦ 1 + eulerCorrection p n) :=
    multipliable_one_add_of_summable (by
      simpa only [Real.norm_eq_abs, habs] using hs)
  refine hm.congr ?_
  intro n
  symm
  apply euler_factor_eq_one_add
  have := eulerCorrection_nonneg hp n
  have hp0 : 0 < p := by linarith
  have hq1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hpow : p⁻¹ ^ (n + 1) < 1 :=
    (pow_lt_one₀ (inv_pos.mpr hp0).le hq1 (by omega))
  linarith
end SharpIntermediateSubgroupBounds
