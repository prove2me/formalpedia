-- Prove2me | solution 1 for RiskControl.UCB.failure_point
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:13:28.74441+00:00
-- url     : https://prove2.me/submissions/1f0bf98f-3d48-43cc-abe4-4ac39624b611

import Mathlib

theorem solution (Λ : Set EReal) (hΛ : IsClosed Λ) (R : EReal → ℝ)
    (hcont : ContinuousOn R Λ) (α : ℝ) (hU : {l ∈ Λ | α < R l}.Nonempty) :
    sSup {l ∈ Λ | α < R l} ∈ Λ ∧ α ≤ R (sSup {l ∈ Λ | α < R l}) := by
  have hc : IsClosed {l ∈ Λ | α ≤ R l} := hΛ.isClosed_le continuousOn_const hcont
  have hs : {l ∈ Λ | α < R l} ⊆ {l ∈ Λ | α ≤ R l} := fun l h => ⟨h.1, h.2.le⟩
  exact (closure_minimal hs hc) (sSup_mem_closure hU)

#print axioms solution
