-- Prove2me | solution 1 for SteinitzExchange.Extension.exc_add_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T10:21:39.246986+00:00
-- url     : https://prove2.me/submissions/65b90013-d8c6-4928-857a-3be72507b158

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

open SteinitzExchange.Extension

/-- The perturbation terms of a pair of points are unchanged by the exchange
`(x, y) ↦ (x − χ_u + χ_v, y + χ_u − χ_v)`, because the two exchanged points have
the same coordinate sum as the two original ones. -/
theorem pairing_add_cancel {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ)
    (x y : V → ℤ) (u v : V) :
    pairing p (toReal x) + pairing p (toReal y)
      = pairing p (toReal (x - chi u + chi v)) + pairing p (toReal (y + chi u - chi v)) := by
  have key : ∀ a b : V → ℤ,
      pairing p (toReal a) + pairing p (toReal b)
        = ∑ w, (p w * toReal a w + p w * toReal b w) := by
    intro a b
    simp only [pairing, Finset.sum_add_distrib, Pi.add_apply]
  rw [key x y, key (x - chi u + chi v) (y + chi u - chi v)]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Pi.add_apply, Pi.sub_apply, toReal]
  push_cast
  ring

/-- Linearity lets one add a perturbation to an (EXC) inequality for free. -/
private theorem exc_ineq_perturb {V : Type*} [Fintype V] (ω : (V → ℤ) → ℝ) (p : V → ℝ)
    (x y x' y' : V → ℤ)
    (hw : ω x + ω y ≤ ω x' + ω y')
    (hp : pairing p (toReal x) + pairing p (toReal y)
          = pairing p (toReal x') + pairing p (toReal y')) :
    perturb ω p x + perturb ω p y ≤ perturb ω p x' + perturb ω p y' := by
  calc perturb ω p x + perturb ω p y
      = (ω x + ω y) + (pairing p (toReal x) + pairing p (toReal y)) := by
        unfold perturb; ring
    _ ≤ (ω x' + ω y') + (pairing p (toReal x') + pairing p (toReal y')) :=
        add_le_add hw hp.le
    _ = perturb ω p x' + perturb ω p y' := by
        unfold perturb; ring

/-- Murota 1996, p. 280, Theorem 2.2 (under the standing assumption of §2.3 that `ω` satisfies
(EXC)): `ω[p]` satisfies (EXC) for every `p : V → ℝ`. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) (p : V → ℝ) :
    SatisfiesEXC B (perturb ω p) := by
  intro x hx y hy u hu
  obtain ⟨v, hv, hx', hy', hineq⟩ := hω x hx y hy u hu
  exact ⟨v, hv, hx', hy',
    exc_ineq_perturb ω p x y (x - chi u + chi v) (y + chi u - chi v) hineq
      (pairing_add_cancel p x y u v)⟩
