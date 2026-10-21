-- Prove2me | solution 1 for RoboAdvising.Interaction.f_strictMono_of_beta_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:54:24.901355+00:00
-- url     : https://prove2.me/submissions/0b449f62-8624-49c2-be0b-a41f46841007

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

set_option autoImplicit false
open RoboAdvising.Interaction

theorem solution (P : Params) (hS : P.Standing) (hβ : P.β = 0) (hpe : 0 < P.pe) :
    StrictMonoOn (fAux P) (Set.Ici 1) ∧ fAux P 1 = 0 := by
  obtain ⟨h0, hse, hp0, hp1, hβ'⟩ := hS
  have e : ∀ φ : ℝ, fAux P φ = P.se * ((φ - 1) / 2 * P.pe) := by
    intro φ
    unfold fAux
    rw [hβ]
    have : Real.sqrt (P.se ^ 2) = P.se := Real.sqrt_sq hse.le
    simp [this]
    ring
  refine ⟨?_, by rw [e]; ring⟩
  intro x hx y hy hxy
  rw [e, e]
  have : (x - 1) / 2 * P.pe < (y - 1) / 2 * P.pe := by
    apply mul_lt_mul_of_pos_right _ hpe
    linarith
  exact mul_lt_mul_of_pos_left this hse
