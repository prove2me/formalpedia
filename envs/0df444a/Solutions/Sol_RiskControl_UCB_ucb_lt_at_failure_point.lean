-- Prove2me | solution 1 for RiskControl.UCB.ucb_lt_at_failure_point
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:13:30.734976+00:00
-- url     : https://prove2.me/submissions/fe1813d9-cda8-4218-b4b9-4bf7b1ab3638

import Mathlib
import Definitions.Def_RiskControl_UCB_Setting

open RiskControl.UCB

theorem solution (Λ : Set EReal) (hΛ : IsClosed Λ) (R : EReal → ℝ)
    (hcont : ContinuousOn R Λ) (r : EReal → ℝ) (α : ℝ)
    (hS : (calSet Λ r α).Nonempty) (hfail : α < R (lambdaHat Λ r α)) :
    {l ∈ Λ | α < R l}.Nonempty ∧ r (sSup {l ∈ Λ | α < R l}) < α := by
  have hbad : ∃ l ∈ calSet Λ r α, α < R l := by
    by_contra! hn
    have hc : IsClosed {l ∈ Λ | R l ≤ α} := hΛ.isClosed_le hcont continuousOn_const
    have hs : calSet Λ r α ⊆ {l ∈ Λ | R l ≤ α} := fun l h => ⟨h.1, hn l h⟩
    have hi := closure_minimal hs hc (sInf_mem_closure hS)
    exact (not_le_of_gt hfail) hi.2
  obtain ⟨l, hl, hr⟩ := hbad
  have hU : {l ∈ Λ | α < R l}.Nonempty := ⟨l, hl.1, hr⟩
  refine ⟨hU, hl.2 _ ?_ (le_sSup ⟨hl.1, hr⟩)⟩
  exact closure_minimal (fun _ h => h.1) hΛ (sSup_mem_closure hU)

#print axioms solution
