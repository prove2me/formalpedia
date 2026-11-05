-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.orthocomplement_bounds_and_order
-- status  : ACCEPTED   (prove)
-- author  : @21604
-- created : 2026-11-04T17:55:03.538805+00:00
-- url     : https://prove2.me/submissions/84b7be32-cb2d-4b0f-9c02-201449b1f745

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

universe u

open Set TopologicalSpace
open QAlgorithms.Papers.Independent.Intakethird100.P20

/-- rem-2.1; de Groote, Observables I, PDF p. 20. The order-reversing behavior of the designated
orthocomplement and its values at the two bounds, derived from IsOrthocomplement:
perp ⊥ = ⊤ and perp ⊤ = ⊥ are the lattice identities ⊥ ⊔ x = x and ⊤ ⊓ x = x applied to
the defining orthogonal-complement identities, and  ≤ b ↔ perp b ≤ perp a follows by applying
perp (an involution swapping ⊓ and ⊔) to  ⊔ b = b and back. -/
theorem solution {L : Type u} [Lattice L] [BoundedOrder L]
    (perp : L → L) (hperp : IsOrthocomplement perp) :
    perp ⊥ = ⊤ ∧ perp ⊤ = ⊥ ∧ ∀ a b : L, a ≤ b ↔ perp b ≤ perp a := by
  obtain ⟨h1, h2, h3⟩ := hperp
  refine ⟨?_, ?_, ?_⟩
  · have h := (h1 ⊥).2
    simpa using h
  · have h := (h1 ⊤).1
    simpa using h
  · intro a b
    constructor
    · intro hab
      have hsup : a ⊔ b = b := sup_eq_right.2 hab
      calc perp b = perp (a ⊔ b) := by rw [hsup]
        _ = perp a ⊓ perp b := (h2 a b).2
        _ ≤ perp a := inf_le_left
    · intro hba
      have hinf : perp a ⊓ perp b = perp b := inf_eq_right.2 hba
      have h := congrArg perp hinf
      rw [(h2 (perp a) (perp b)).1, h3 a, h3 b] at h
      exact le_trans le_sup_left (le_of_eq h)

end
