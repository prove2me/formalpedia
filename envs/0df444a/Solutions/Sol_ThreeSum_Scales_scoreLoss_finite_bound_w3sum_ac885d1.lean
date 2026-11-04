-- Prove2me | solution 1 for ThreeSum.Scales.scoreLoss_finite_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:24.257203+00:00
-- url     : https://prove2.me/submissions/8ed04695-8ee3-4545-92d4-3acf635fd4ad

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Sqrt
import Definitions.Def_Submission_ThreeSum_Scales
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution {k n H H₁ P : ℕ}
    (hC : 0 < (PrimeDensity.candidates (primeWindow n)).card)
    (hbudget : divisorBudget k n * primeWindow n ≤
      (PrimeDensity.candidates (primeWindow n)).card * (4 * (k + 2) * (inputBits n + 1)))
    (hcontract : (PrimeDensity.candidates (primeWindow n)).card ^ primeDepth radix n * H ≤
      divisorBudget k n ^ primeDepth radix n * H₁)
    (hP : P ≤ (4 * primeWindow n) ^ primeDepth radix n) :
    P * H ≤ scoreLoss k n * H₁ := by
  let C := (PrimeDensity.candidates (primeWindow n)).card
  let r := primeDepth radix n
  let A := 4 * (k + 2) * (inputBits n + 1)
  have hpow := Nat.pow_le_pow_left hbudget r
  have hbig : C ^ r * (primeWindow n ^ r * H) ≤ C ^ r * (A ^ r * H₁) := by
    calc
      C ^ r * (primeWindow n ^ r * H) = primeWindow n ^ r * (C ^ r * H) := by ring
      _ ≤ primeWindow n ^ r * (divisorBudget k n ^ r * H₁) :=
        Nat.mul_le_mul_left _ hcontract
      _ = (divisorBudget k n * primeWindow n) ^ r * H₁ := by rw [mul_pow]; ring
      _ ≤ (C * A) ^ r * H₁ := Nat.mul_le_mul_right _ hpow
      _ = C ^ r * (A ^ r * H₁) := by rw [mul_pow]; ring
  have hsmall : primeWindow n ^ r * H ≤ A ^ r * H₁ :=
    Nat.le_of_mul_le_mul_left hbig (Nat.pow_pos hC)
  calc
    P * H ≤ (4 * primeWindow n) ^ r * H := Nat.mul_le_mul_right _ hP
    _ = 4 ^ r * (primeWindow n ^ r * H) := by rw [mul_pow]; ring
    _ ≤ 4 ^ r * (A ^ r * H₁) := Nat.mul_le_mul_left _ hsmall
    _ = scoreLoss k n * H₁ := by
      rw [← mul_assoc, ← mul_pow]
      have heq : 4 * A = 16 * (k + 2) * (inputBits n + 1) := by dsimp [A]; ring
      rw [heq]
      rfl
end ThreeSum.Scales
