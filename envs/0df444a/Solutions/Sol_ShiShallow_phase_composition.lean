-- Prove2me | solution 1 for ShiShallow.phase_composition
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T05:44:52.98298+00:00
-- url     : https://prove2.me/submissions/84e61008-bdfd-4023-a44d-f72a0e0c8f03

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

open ShiShallow

theorem solution {n : ℕ} (f g : QState n → QState n) (a b : Bits n → ℂ)
    (hf : ∀ (φ : QState n) (x : Bits n), f φ x = a x * φ x)
    (hg : ∀ (φ : QState n) (x : Bits n), g φ x = b x * φ x)
    (ψ : QState n) :
    ∀ x : Bits n, g (f ψ) x = (b x * a x) * ψ x := by
  intro x
  rw [hg (f ψ) x, hf ψ x]
  ring
