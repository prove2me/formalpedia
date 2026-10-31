-- Prove2me | solution 1 for PegProtect.Equilibrium.equation_3_5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:36:07.683994+00:00
-- url     : https://prove2.me/submissions/f5156832-14ef-44f2-b27e-d25516edcc92

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model
open PegProtect.Equilibrium

theorem solution(P : Params) (hP : P.Standing) (ω Nr : ℝ)
    (h0 : 0 ≤ ω) (h1 : ω < 1) (hNr : 0 < Nr) :
    piR P ω Nr = 2 * ((1 - ω) * P.ρ / ((1 + ω) * Nr)) - 2 * P.ν := by
  obtain ⟨hc, hd0, hd1, hphi, hδ, hρ, hν⟩ := hP
  have hq0 : ∀ n : ℕ, q ω (n : ℤ) = (1 - ω) / (1 + ω) * ω ^ n := by
    intro n; unfold q; rw [Int.natAbs_natCast]
  have hq1 : ∀ n : ℕ, q ω (-((n : ℤ) + 1)) = (1 - ω) / (1 + ω) * ω * ω ^ n := by
    intro n; unfold q; rw [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega]; ring
  have hS0 : ∑' n : ℕ, q ω (n : ℤ) = 1 / (1 + ω) := by
    simp only [hq0]; rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
    have : (1 - ω) ≠ 0 := by linarith
    have : (1 + ω) ≠ 0 := by linarith
    field_simp
  have hS1 : ∑' n : ℕ, q ω (-((n : ℤ) + 1)) = ω / (1 + ω) := by
    simp only [hq1]; rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
    have : (1 - ω) ≠ 0 := by linarith
    have : (1 + ω) ≠ 0 := by linarith
    field_simp
  unfold piR; rw [hS0]
  have : (1 + ω) ≠ 0 := by linarith
  field_simp
