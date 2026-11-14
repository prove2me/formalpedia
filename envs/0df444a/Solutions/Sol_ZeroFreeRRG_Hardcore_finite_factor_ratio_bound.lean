-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.finite_factor_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:15:38.277287+00:00
-- url     : https://prove2.me/submissions/ec141811-aeb9-442d-bc28-6334ecb700b7

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem solution {A : Type*} [Fintype A] (p : A → ℝ) (J : A → A → ℝ)
    (hp : ∀ a, 0 < p a) :
    ∃ C : ℝ, 1 ≤ C ∧ (∀ a b, p a ≤ C * p b) ∧
      (∀ a b c d, 0 < J c d → J a b ≤ C * J c d) := by
  classical
  obtain ⟨u, hu⟩ := Finite.bddAbove_range (fun x : A × A => p x.1 / p x.2)
  obtain ⟨v, hv⟩ := Finite.bddAbove_range (fun x : (A × A) × (A × A) =>
    J x.1.1 x.1.2 / J x.2.1 x.2.2)
  let C := max 1 (max u v)
  have h1 : 1 ≤ C := le_max_left _ _
  have h2 : u ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have h3 : v ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, h1, ?_, ?_⟩
  · intro a b
    apply (div_le_iff₀ (hp b)).mp
    exact le_trans (hu ⟨(a,b), rfl⟩) h2
  · intro a b c d hJ
    apply (div_le_iff₀ hJ).mp
    exact le_trans (hv ⟨((a,b),(c,d)), rfl⟩) h3
