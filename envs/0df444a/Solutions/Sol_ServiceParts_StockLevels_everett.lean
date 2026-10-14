-- Prove2me | solution 1 for ServiceParts.StockLevels.everett
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:26:00.802365+00:00
-- url     : https://prove2.me/submissions/e737afce-5623-4148-a490-4b9cdd95ac7f

import Mathlib



namespace ServiceParts.StockLevels

theorem everett_core {X : Type*} (S : Set X) (f g : X → ℝ) (b θ : ℝ) (hθ : 0 ≤ θ)
    (x0 : X) (hx0 : x0 ∈ S)
    (hopt : ∀ x ∈ S, f x0 + θ * (g x0 - b) ≤ f x + θ * (g x - b)) :
    IsLeast (f '' {x | x ∈ S ∧ g x ≤ g x0}) (f x0) := by
  refine ⟨⟨x0, ⟨hx0, le_rfl⟩, rfl⟩, ?_⟩
  rintro _ ⟨x, ⟨hxS, hgx⟩, rfl⟩
  have h1 := hopt x hxS
  nlinarith [mul_le_mul_of_nonneg_left hgx hθ]

end ServiceParts.StockLevels

open ServiceParts.StockLevels


theorem solution {X : Type*} (S : Set X) (f g : X → ℝ) (b θ : ℝ) (hθ : 0 ≤ θ)
    (x0 : X) (hx0 : x0 ∈ S)
    (hopt : ∀ x ∈ S, f x0 + θ * (g x0 - b) ≤ f x + θ * (g x - b)) :
    IsLeast (f '' {x | x ∈ S ∧ g x ≤ g x0}) (f x0) := by
  exact everett_core S f g b θ hθ x0 hx0 hopt
