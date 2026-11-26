-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.summable_eulerCorrection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:53:20.462637+00:00
-- url     : https://prove2.me/submissions/e60b9b58-be9f-4ff8-91f8-1f3bee9a714b

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
section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
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
private lemma eulerCorrection_le {p : ℝ} (hp : 2 ≤ p) (n : ℕ) :
    eulerCorrection p n ≤ 2 * p⁻¹ ^ (n + 1) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ p⁻¹ := (inv_pos.mpr hp0).le
  have hq_half : p⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
  have ht0 : 0 ≤ p⁻¹ ^ (n + 1) := pow_nonneg hq0 _
  have ht_half : p⁻¹ ^ (n + 1) ≤ (2 : ℝ)⁻¹ := by
    calc
      p⁻¹ ^ (n + 1) ≤ p⁻¹ ^ 1 :=
        pow_le_pow_of_le_one hq0 (hq_half.trans (by norm_num)) (by omega)
      _ ≤ (2 : ℝ)⁻¹ := by simpa using hq_half
  rw [eulerCorrection, div_le_iff₀ (by linarith : 0 < 1 - p⁻¹ ^ (n + 1))]
  nlinarith [mul_nonneg ht0 (sub_nonneg.mpr (by linarith : 2 * p⁻¹ ^ (n + 1) ≤ 1))]
end SharpIntermediateSubgroupBounds
end

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℝ} (hp : 2 ≤ p) :
    Summable (eulerCorrection p) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ p⁻¹ := (inv_pos.mpr hp0).le
  have hq1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hgeom : Summable (fun n : ℕ ↦ p⁻¹ ^ (n + 1)) := by
    simpa using (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq0 hq1)
  exact (hgeom.mul_left 2).of_nonneg_of_le
    (fun n ↦ eulerCorrection_nonneg hp n) (fun n ↦ eulerCorrection_le hp n)
end SharpIntermediateSubgroupBounds
