-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gammaR_inv_lt_eulerC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:27.413269+00:00
-- url     : https://prove2.me/submissions/7dc03c8d-97b0-4211-9b03-7f2436f2f149

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
theorem _root_.solution {p : ℝ} (hp : 2 ≤ p) (r : ℕ) :
    (gammaR p r)⁻¹ < eulerC p := by
  have hfinite : (gammaR p r)⁻¹ =
      ∏ n ∈ Finset.range r, (1 - p⁻¹ ^ (n + 1))⁻¹ := by
    simp [gammaR, Finset.prod_inv_distrib]
  rw [hfinite]
  have hs := euler_partial_strictMono hp
  have hle := hs.monotone.ge_of_tendsto (eulerC_partial_tendsto hp) (r + 1)
  exact (hs (Nat.lt_succ_self r)).trans_le hle
end SharpIntermediateSubgroupBounds
