-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.eulerC_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:26.389233+00:00
-- url     : https://prove2.me/submissions/892deec3-ec6c-4837-9221-3c99ae0b0478

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_eulerC_partial_tendsto
section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
private lemma euler_partial_pos {p : ℝ} (hp : 2 ≤ p) (r : ℕ) :
    0 < ∏ n ∈ Finset.range r, (1 - p⁻¹ ^ (n + 1))⁻¹ := by
  apply Finset.prod_pos
  intro n hn
  have hp0 : 0 < p := by linarith
  have hq1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  exact inv_pos.mpr (sub_pos.mpr (pow_lt_one₀ (inv_pos.mpr hp0).le hq1 (by omega)))
private lemma euler_partial_strictMono {p : ℝ} (hp : 2 ≤ p) :
    StrictMono (fun r : ℕ ↦ ∏ n ∈ Finset.range r, (1 - p⁻¹ ^ (n + 1))⁻¹) := by
  apply strictMono_nat_of_lt_succ
  intro r
  rw [Finset.prod_range_succ]
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < p⁻¹ ^ (r + 1) := pow_pos (inv_pos.mpr hp0) _
  have hq1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hden : 0 < 1 - p⁻¹ ^ (r + 1) :=
    sub_pos.mpr (pow_lt_one₀ (inv_pos.mpr hp0).le hq1 (by omega))
  have hfactor : 1 < (1 - p⁻¹ ^ (r + 1))⁻¹ := by
    exact (one_lt_inv₀ hden).2 (by linarith)
  nlinarith [euler_partial_pos hp r]
end SharpIntermediateSubgroupBounds
end

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℝ} (hp : 2 ≤ p) : 0 < eulerC p := by
  have hmono := (euler_partial_strictMono hp).monotone
  have hlim := eulerC_partial_tendsto hp
  have hle := hmono.ge_of_tendsto hlim 1
  have hzero : (1 : ℝ) < ∏ n ∈ Finset.range 1,
      (1 - p⁻¹ ^ (n + 1))⁻¹ := by
    simpa using (euler_partial_strictMono hp (Nat.zero_lt_one))
  linarith
end SharpIntermediateSubgroupBounds
