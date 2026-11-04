-- Prove2me | solution 1 for ThreeSum.Scales.primeDepth_loss_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:44:37.654531+00:00
-- url     : https://prove2.me/submissions/330a0abf-76fb-49b7-b534-005bbd959e10

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
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two
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
theorem _root_.solution (R : ℕ → ℕ) {n P : ℕ}
    (hP : primeWindow n ^ primeDepth R n ≤ P) :
    R n ≤ primeLoss R n * P := by
  have hy := primeWindow_ge_two n
  have hr := Nat.lt_pow_succ_log_self (by omega : 1 < 4 * primeWindow n) (R n / 4)
  simp only [Nat.succ_eq_add_one] at hr
  have hmod := Nat.mod_lt (R n) (by decide : 0 < 4)
  have hdiv := Nat.mod_add_div (R n) 4
  have hbase : R n < 4 * (4 * primeWindow n) ^ (primeDepth R n + 1) := by
    simp only [primeDepth] at ⊢
    omega
  have heq : 4 * (4 * primeWindow n) ^ (primeDepth R n + 1) =
      16 * primeWindow n * 4 ^ primeDepth R n * primeWindow n ^ primeDepth R n := by
    rw [pow_succ, mul_pow]
    ring
  rw [heq] at hbase
  have hm := Nat.mul_le_mul_left (16 * primeWindow n * 4 ^ primeDepth R n) hP
  apply hbase.le.trans (hm.trans ?_)
  unfold primeLoss
  nlinarith [Nat.zero_le (primeWindow n * 4 ^ primeDepth R n * P)]
end ThreeSum.Scales
