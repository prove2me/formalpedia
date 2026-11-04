-- Prove2me | solution 1 for ThreeSum.BudgetTime.endStatementBigO_of_eventually_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:54:13.180246+00:00
-- url     : https://prove2.me/submissions/f8eabc1b-1442-416b-88f6-5c4035c2c327

import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Theorems.Thm_ThreeSum_BudgetTime_rational_rpow_power
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.BudgetTime
open Filter Real ThreeSum.Parameters ThreeSum.StageBounds
  ThreeSum.UniformStageBounds
open scoped Topology
set_option maxHeartbeats 400000
namespace ThreeSum.BudgetTime
theorem _root_.solution {r : ℚ} {T : ℕ → ℕ}
    (hr : 0 ≤ r)
    (hT : ∀ᶠ n : ℕ in atTop, (T n : ℝ) ≤ (n : ℝ) ^ (r : ℝ)) :
    EndStatement.BigO T r := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hT
  let K : ℕ := 1 + ∑ i ∈ Finset.range N, T i ^ r.den
  refine ⟨K, ?_⟩
  intro n hn
  have hK : 1 ≤ K := by dsimp [K]; omega
  by_cases hnN : N ≤ n
  · have hreal := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (T n)) (hN n hnN) r.den
    rw [rational_rpow_power hr] at hreal
    have hnat : T n ^ r.den ≤ n ^ r.num.toNat := by exact_mod_cast hreal
    exact hnat.trans (Nat.le_mul_of_pos_left _ hK)
  · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hterm : T n ^ r.den ≤ ∑ i ∈ Finset.range N, T i ^ r.den :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (T i ^ r.den)) hmem
    have hTK : T n ^ r.den ≤ K := hterm.trans (by dsimp [K]; omega)
    have hnpow : 1 ≤ n ^ r.num.toNat := Nat.one_le_pow _ _ (by omega)
    exact hTK.trans (Nat.le_mul_of_pos_right _ hnpow)
end ThreeSum.BudgetTime
