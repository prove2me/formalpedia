-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_of_finite_predicate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:04:13.678043+00:00
-- url     : https://prove2.me/submissions/afc0f872-6960-468d-b588-2c4b4046393d

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Finite α] [PartialOrder α] (P : α → Prop)
    (hne : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, a ≤ b → P b → b = a := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨b, hab, hb⟩ := Finite.exists_le_maximal (p := P) ha
  exact ⟨b, hb.1, fun c hbc hc => le_antisymm (hb.2 hc hbc) hbc⟩