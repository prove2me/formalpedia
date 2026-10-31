-- Prove2me | solution 1 for PegProtect.Equilibrium.equation_3_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:34:51.70331+00:00
-- url     : https://prove2.me/submissions/9b68b985-1602-411f-89dd-067153d3357c

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model
open PegProtect.Equilibrium

theorem solution(P : Params) (hP : P.Standing) (ω : ℝ) (h0 : 0 ≤ ω) (h1 : ω < 1) :
    piM P ω = (P.phi - P.d) / (1 + ω) * ω + (P.phi - 1) / (1 + ω) := by
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
  have hM' : piM P ω = (P.phi - P.d) / (1 + ω) * ω + (P.phi - 1) / (1 + ω) := by
    unfold piM; rw [hS1, hS0]; ring
  exact hM'
