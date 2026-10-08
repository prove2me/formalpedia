-- Prove2me | solution 1 for TeschlODE.Shared.flow_comp_add_isIntegralCurve
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:55:01.463963+00:00
-- url     : https://prove2.me/submissions/cc55dcde-a8a7-41dd-b776-944ee4d12648

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

open TeschlODE.Shared in
theorem solution {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M) (I : (Fin n → ℝ) → Set ℝ)
    (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : IsMaximalFlow f M I Φ) (x : Fin n → ℝ)
    (hx : x ∈ M) (c : ℝ) :
    IsIntegralCurve f M {s | s + c ∈ I x} (fun s => Φ (s + c) x) := by
  obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := hΦ x hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h1.preimage (continuous_id.add continuous_const)
  · refine ⟨fun a ha b hb t ht => ?_⟩
    exact h2.out ha hb ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t ht
    exact h3 (t + c) ht
  · intro t ht
    exact (h4 (t + c) ht).comp_add_const t c

