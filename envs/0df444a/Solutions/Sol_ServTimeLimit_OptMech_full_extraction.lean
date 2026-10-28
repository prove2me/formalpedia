-- Prove2me | solution 1 for ServTimeLimit.OptMech.full_extraction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:10:34.49569+00:00
-- url     : https://prove2.me/submissions/312a9e4d-a394-4b22-b50d-e1a2a08fae9b

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model

open MeasureTheory ServTimeLimit.OptMech in
theorem solution (P : Params) (hP : P.Standing) (Φ : Set ℝ) (t : ℝ → ℝ)
    (hA : IsAllocation P Φ t) (p : ℝ → ℝ)
    (hp : ∀ θ, p θ = min θ (t θ) - P.c * waitTime P Φ t) :
    IsIC Φ t p ∧
    (∀ θ ∈ Φ, min (t θ) θ - p θ - P.c * waitTime P Φ t = 0) ∧
    (∀ θ ∈ Set.Icc 0 P.θbar \ Φ, ∀ θ' ∈ Φ, min (t θ') θ - p θ' - P.c * waitTime P Φ t ≤ 0) ∧
    revenue P Φ p = welfare P Φ t := by
  have hle : ∀ θ ∈ Φ, t θ ≤ θ := fun θ hθ => (hA.2.2.2.1 θ hθ).2
  have key : ∀ θ ∈ Φ, p θ = t θ - P.c * waitTime P Φ t := by
    intro θ hθ; rw [hp, min_eq_right (hle θ hθ)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ hθ θ' hθ'
    rw [key θ hθ, key θ' hθ', min_eq_left (hle θ hθ)]
    have := min_le_left (t θ') θ
    linarith
  · intro θ hθ
    rw [key θ hθ, min_eq_left (hle θ hθ)]; ring
  · intro θ _ θ' hθ'
    rw [key θ' hθ']
    have := min_le_left (t θ') θ
    linarith
  · unfold revenue welfare
    congr 1
    exact setIntegral_congr_fun hA.1 (fun θ hθ => key θ hθ)
