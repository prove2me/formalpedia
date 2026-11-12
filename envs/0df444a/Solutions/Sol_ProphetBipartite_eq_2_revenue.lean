-- Prove2me | solution 1 for ProphetBipartite.eq_2_revenue
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:22:45.107819+00:00
-- url     : https://prove2.me/submissions/c0a856a9-0885-4004-94dc-4bb660442f53

import Mathlib
import Definitions.Def_ProphetBipartite_vaddRun

open MeasureTheory
open scoped NNReal ENNReal

namespace Aux_PB2

open ProphetBipartite

def Inv {L R E : Type*} (left : E → L) (l : L → ℝ≥0) (right : E → R) (r : R → ℝ≥0)
    (s : RunState L R E) : Prop :=
  (∑ e ∈ s.accepted, (l (left e) + r (right e)) =
    ∑ i ∈ s.coveredL, l i + ∑ j ∈ s.coveredR, r j) ∧ ∀ e ∈ s.accepted, left e ∈ s.coveredL

theorem inv_step {L R E : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (v : E → ℝ≥0)
    (s : RunState L R E) (e : E) (hs : Inv left l right r s) :
    Inv left l right r (vaddStep left right l r v s e) := by
  unfold vaddStep
  split_ifs with h
  · obtain ⟨hL, hR, _⟩ := h
    have he : e ∉ s.accepted := fun he => hL (hs.2 e he)
    refine ⟨?_, ?_⟩
    · show ∑ x ∈ insert e s.accepted, (l (left x) + r (right x)) =
        ∑ i ∈ insert (left e) s.coveredL, l i + ∑ j ∈ insert (right e) s.coveredR, r j
      rw [Finset.sum_insert he, Finset.sum_insert hL, Finset.sum_insert hR, hs.1]
      ring
    · intro e' he'
      show left e' ∈ insert (left e) s.coveredL
      rcases Finset.mem_insert.mp he' with rfl | h'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hs.2 e' h')
  · exact hs

theorem inv_fold {L R E : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (v : E → ℝ≥0)
    (σ : List E) : ∀ s : RunState L R E, Inv left l right r s →
      Inv left l right r (σ.foldl (vaddStep left right l r v) s) := by
  induction σ with
  | nil => intro s hs; exact hs
  | cons e σ ih => intro s hs; exact ih _ (inv_step left right l r v s e hs)

end Aux_PB2

open ProphetBipartite in
theorem solution {L R E : Type*} [Fintype E] [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0) [∀ e, IsProbabilityMeasure (μ e)]
    (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E) :
    (∀ v : E → ℝ≥0, ∑ e ∈ vaddAccepted left right l r σ v, (l (left e) + r (right e)) =
        ∑ i ∈ vaddCoveredL left right l r σ v, l i + ∑ j ∈ vaddCoveredR left right l r σ v, r j) ∧
      ∫⁻ v, ((∑ e ∈ vaddAccepted left right l r σ v, (l (left e) + r (right e)) : ℝ≥0) : ℝ≥0∞)
          ∂(Measure.pi μ) =
        ∫⁻ v, ((∑ i ∈ vaddCoveredL left right l r σ v, l i +
            ∑ j ∈ vaddCoveredR left right l r σ v, r j : ℝ≥0) : ℝ≥0∞) ∂(Measure.pi μ) := by
  have h1 : ∀ v : E → ℝ≥0, ∑ e ∈ vaddAccepted left right l r σ v, (l (left e) + r (right e)) =
      ∑ i ∈ vaddCoveredL left right l r σ v, l i + ∑ j ∈ vaddCoveredR left right l r σ v, r j := by
    intro v
    have h0 : Aux_PB2.Inv left l right r (⟨∅, ∅, ∅⟩ : RunState L R E) := by
      refine ⟨?_, ?_⟩
      · simp
      · intro e he
        simp at he
    exact (Aux_PB2.inv_fold left right l r v σ _ h0).1
  refine ⟨h1, ?_⟩
  refine lintegral_congr fun v => ?_
  rw [h1 v]
