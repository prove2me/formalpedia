-- Prove2me | solution 1 for ProxADMMLC.Conv.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:08:53.077573+00:00
-- url     : https://prove2.me/submissions/878a966d-6754-4947-9c19-d604e5a7dc52

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

open ProxADMMLC.Conv


theorem solution {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (Γ p c α β : ℝ) (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (x z : ℕ → E n) (y : ℕ → E m) (hrun : IsRun f A b ℓ u Γ p c α β x y z) :
    ∀ t, dval f A b Γ p xs (y (t + 1)) (z (t + 1)) - dval f A b Γ p xs (y t) (z t) ≥
      α * inner ℝ (A (x t) - b) (A (xs (y (t + 1)) (z t)) - b) +
        p / 2 * inner ℝ (z (t + 1) - z t)
          (z (t + 1) + z t - (2 : ℝ) • xs (y (t + 1)) (z (t + 1))) := by
  intro t
  obtain ⟨hy, -, hz⟩ := hrun.2.2 t
  set X1 := xs (y (t + 1)) (z (t + 1))
  set X2 := xs (y (t + 1)) (z t)
  set X3 := xs (y t) (z t)
  have k1 : K f A b Γ p X2 (z t) (y (t + 1)) ≤ K f A b Γ p X1 (z t) (y (t + 1)) :=
    (hxs (y (t + 1)) (z t)).2 X1 (hxs (y (t + 1)) (z (t + 1))).1
  have k2 : K f A b Γ p X3 (z t) (y t) ≤ K f A b Γ p X2 (z t) (y t) :=
    (hxs (y t) (z t)).2 X2 (hxs (y (t + 1)) (z t)).1
  have e1 : K f A b Γ p X1 (z (t + 1)) (y (t + 1)) - K f A b Γ p X1 (z t) (y (t + 1))
      = p / 2 * inner ℝ (z (t + 1) - z t) (z (t + 1) + z t - (2 : ℝ) • X1) := by
    unfold K
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_right, real_inner_comm (z t) (z (t + 1)), real_inner_comm X1 (z t),
      real_inner_comm X1 (z (t + 1))]
    ring
  have e2 : K f A b Γ p X2 (z t) (y (t + 1)) - K f A b Γ p X2 (z t) (y t)
      = α * inner ℝ (A (x t) - b) (A X2 - b) := by
    unfold K
    rw [hy, inner_add_left, real_inner_smul_left]
    ring
  unfold dval
  linarith
