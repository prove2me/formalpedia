-- Prove2me | solution 1 for QMCLeafB.SnapLedger.ledger_round_ok
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T12:40:43.81945+00:00
-- url     : https://prove2.me/submissions/dea374df-a646-4453-960e-da98a8a97fe7

import Mathlib
open Finset

theorem solution {k : ℕ} {S : Set (Fin k → ℝ)} {c a a' : Fin k → ℝ} {m C ε rho sigma : ℝ}
    (hsep : ∀ z ∈ S, -m ≤ ∑ i, c i * (z i - a i))
    (hC : Real.sqrt (∑ i, (c i) ^ 2) ≤ C)
    (hε : Real.sqrt (∑ i, (a i - a' i) ^ 2) ≤ ε) (hm : 0 < m) (hε0 : 0 ≤ ε)
    (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hroom : (m + C * ε) ^ 2 ≤ rho ^ 2 * sigma) :
    0 ≤ m + C * ε ∧ (m + C * ε) ^ 2 ≤ rho ^ 2 * sigma ∧
      ∀ z ∈ S, -(m + C * ε) ≤ ∑ i, c i * (z i - a' i) := by
  have hC0 : 0 ≤ C := (Real.sqrt_nonneg _).trans hC
  have hε0' : 0 ≤ ε := hε0
  have hmul : Real.sqrt (∑ i, (c i) ^ 2) * Real.sqrt (∑ i, (a i - a' i) ^ 2) ≤ C * ε :=
    mul_le_mul hC hε (Real.sqrt_nonneg _) hC0
  -- Cauchy–Schwarz, applied to `-c`, gives the lower bound on the shift term.
  have hlow : -(C * ε) ≤ ∑ i, c i * (a i - a' i) := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin k))
      (fun i => -c i) (fun i => a i - a' i)
    have hsq : ∑ i : Fin k, (-c i) ^ 2 = ∑ i : Fin k, (c i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsq] at hcs
    simp only [Finset.sum_neg_distrib, neg_mul] at hcs
    linarith
  have hmulC : 0 ≤ C * ε := mul_nonneg hC0 hε0
  refine ⟨by linarith, hroom, ?_⟩
  intro z hz
  have hz' := hsep z hz
  have hsplit : ∑ i, c i * (z i - a' i) = ∑ i, c i * (z i - a i) + ∑ i, c i * (a i - a' i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsplit]
  linarith
