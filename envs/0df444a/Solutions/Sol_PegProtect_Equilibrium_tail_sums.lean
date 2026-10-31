-- Prove2me | solution 1 for PegProtect.Equilibrium.tail_sums
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:37:24.005488+00:00
-- url     : https://prove2.me/submissions/217e6ef5-bc41-4eaa-a6e7-0e2c74349c0b

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model
open PegProtect.Equilibrium

theorem solution(ω : ℝ) (h0 : 0 ≤ ω) (h1 : ω < 1) :
    HasSum (q ω) 1 ∧
    ∑' n : ℕ, q ω n = 1 / (1 + ω) ∧
    ∑' n : ℕ, q ω (-((n : ℤ) + 1)) = ω / (1 + ω) := by
  have hq0 : ∀ n : ℕ, q ω (n : ℤ) = (1 - ω) / (1 + ω) * ω ^ n := by
    intro n; unfold q; rw [Int.natAbs_natCast]
  have hq1 : ∀ n : ℕ, q ω (-((n : ℤ) + 1)) = (1 - ω) / (1 + ω) * ω * ω ^ n := by
    intro n; unfold q; rw [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega]; ring
  have hne1 : (1 - ω) ≠ 0 := by linarith
  have hne2 : (1 + ω) ≠ 0 := by linarith
  have hA : HasSum (fun n : ℕ => q ω (n : ℤ)) (1 / (1 + ω)) := by
    have := (hasSum_geometric_of_lt_one h0 h1).mul_left ((1 - ω) / (1 + ω))
    simp only [hq0]; rwa [show (1 - ω) / (1 + ω) * (1 - ω)⁻¹ = 1 / (1 + ω) by field_simp] at this
  have hB : HasSum (fun n : ℕ => q ω (-((n : ℤ) + 1))) (ω / (1 + ω)) := by
    have := (hasSum_geometric_of_lt_one h0 h1).mul_left ((1 - ω) / (1 + ω) * ω)
    simp only [hq1]; rwa [show (1 - ω) / (1 + ω) * ω * (1 - ω)⁻¹ = ω / (1 + ω) by field_simp] at this
  refine ⟨?_, hA.tsum_eq, hB.tsum_eq⟩
  have := HasSum.of_nat_of_neg_add_one hA hB
  convert this using 1; field_simp
