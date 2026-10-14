-- Prove2me | solution 1 for RiskControl.UCB.theorem_A_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:13:35.366035+00:00
-- url     : https://prove2.me/submissions/f4416d64-cfe4-44f5-9612-d1d08059e179

import Mathlib
import Definitions.Def_RiskControl_UCB_Setting
open MeasureTheory RiskControl.UCB
private lemma UCBFailure (Λ : Set EReal) (hΛ : IsClosed Λ) (R : EReal → ℝ)
    (hcont : ContinuousOn R Λ) (α : ℝ) (hU : {l ∈ Λ | α < R l}.Nonempty) :
    sSup {l ∈ Λ | α < R l} ∈ Λ ∧ α ≤ R (sSup {l ∈ Λ | α < R l}) := by
  have hc : IsClosed {l ∈ Λ | α ≤ R l} := hΛ.isClosed_le continuousOn_const hcont
  have hs : {l ∈ Λ | α < R l} ⊆ {l ∈ Λ | α ≤ R l} := fun l h => ⟨h.1, h.2.le⟩
  exact (closure_minimal hs hc) (sSup_mem_closure hU)

private lemma UCBPoint (Λ : Set EReal) (hΛ : IsClosed Λ) (R : EReal → ℝ)
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


private lemma ucb_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Λ : Set EReal) (hΛ : IsClosed Λ) (R : EReal → ℝ)
    (hcont : ContinuousOn R Λ) (α δ : ℝ) (Rhat : Ω → EReal → ℝ)
    (hucb : ∀ l ∈ Λ, μ {ω | Rhat ω l < R l} ≤ ENNReal.ofReal δ) :
    μ {ω | (calSet Λ (Rhat ω) α).Nonempty ∧ α < R (lambdaHat Λ (Rhat ω) α)}
      ≤ ENNReal.ofReal δ := by
  classical
  by_cases hU : {l ∈ Λ | α < R l}.Nonempty
  · have hp := UCBFailure Λ hΛ R hcont α hU
    apply le_trans (measure_mono ?_) (hucb _ hp.1)
    intro ω hω
    have h := UCBPoint Λ hΛ R hcont (Rhat ω) α hω.1 hω.2
    exact h.2.trans_le hp.2
  · have he : {ω | (calSet Λ (Rhat ω) α).Nonempty ∧ α < R (lambdaHat Λ (Rhat ω) α)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hU (UCBPoint Λ hΛ R hcont (Rhat ω) α hω.1 hω.2).1
    rw [he, measure_empty]
    exact zero_le

 theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Λ : Set EReal) (hΛ : IsClosed Λ) (R : EReal → ℝ)
    (hanti : AntitoneOn R Λ) (hcont : ContinuousOn R Λ) (α δ : ℝ)
    (hex : ∃ l ∈ Λ, R l ≤ α) (Rhat : Ω → EReal → ℝ)
    (hucb : ∀ l ∈ Λ, μ {ω | Rhat ω l < R l} ≤ ENNReal.ofReal δ) :
    μ {ω | (calSet Λ (Rhat ω) α).Nonempty ∧ α < R (lambdaHat Λ (Rhat ω) α)}
      ≤ ENNReal.ofReal δ := by
  exact ucb_bound μ Λ hΛ R hcont α δ Rhat hucb
#print axioms solution
