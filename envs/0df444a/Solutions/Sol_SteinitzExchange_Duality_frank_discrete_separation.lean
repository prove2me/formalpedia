-- Prove2me | solution 1 for SteinitzExchange.Duality.frank_discrete_separation
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T21:05:52.554539+00:00
-- url     : https://prove2.me/submissions/4e36082e-2976-470f-91d6-7a3c36b91e77

import Theorems.Thm_SteinitzExchange_Duality_frank_separation_real
import Theorems.Thm_SteinitzExchange_Duality_frank_separation_integer

set_option autoImplicit false
open SteinitzExchange.Duality

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (f g : Finset V → ℝ) (hf : IsSubmodular f) (hg : IsSupermodular g)
    (hf0 : f ∅ = 0) (hg0 : g ∅ = 0) (hgf : ∀ X : Finset V, g X ≤ f X) :
    (∃ xs : V → ℝ, ∀ X : Finset V, g X ≤ ∑ v ∈ X, xs v ∧ ∑ v ∈ X, xs v ≤ f X) ∧
    ((∀ X : Finset V, ∃ k : ℤ, f X = k) → (∀ X : Finset V, ∃ k : ℤ, g X = k) →
      ∃ xs : V → ℤ, ∀ X : Finset V,
        g X ≤ ((sumOn xs X : ℤ) : ℝ) ∧ ((sumOn xs X : ℤ) : ℝ) ≤ f X) := by
  refine ⟨frank_separation_real f g hf hg hf0 hg0 hgf, ?_⟩
  intro hfi hgi
  exact frank_separation_integer f g hf hg hf0 hg0 hgf hfi hgi

#print axioms solution
