-- Prove2me | solution 1 for RoboAdvising.Interaction.f_strictAnti_of_pe_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:54:26.115978+00:00
-- url     : https://prove2.me/submissions/759ea47f-1830-449f-8a5f-67e464e9b611

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

set_option autoImplicit false
open RoboAdvising.Interaction

theorem solution (P : Params) (hS : P.Standing) (hpe : P.pe = 0) (hβ : 0 < P.β) :
    StrictAntiOn (fAux P) (Set.Ici 1) ∧
    Filter.Tendsto (fAux P) Filter.atTop (nhds 0) := by
  obtain ⟨h0, hse, hp0, hp1, hβ'⟩ := hS
  have ha : 0 < P.β * P.sig0 := mul_pos hβ h0
  have e : ∀ φ : ℝ, fAux P φ = P.β * P.sig0 * (Real.sqrt φ)⁻¹ := by
    intro φ
    unfold fAux
    rw [hpe]
    simp [div_eq_mul_inv]
  constructor
  · intro x hx y hy hxy
    rw [e, e]
    have hx0 : 0 < Real.sqrt x := Real.sqrt_pos.2 (by have := hx.out; linarith)
    have : Real.sqrt x < Real.sqrt y := Real.sqrt_lt_sqrt (by have := hx.out; linarith) hxy
    exact mul_lt_mul_of_pos_left (inv_strictAnti₀ hx0 this) ha
  · have h1 : Filter.Tendsto Real.sqrt Filter.atTop Filter.atTop :=
      Real.tendsto_sqrt_atTop
    have h2 := (tendsto_inv_atTop_zero.comp h1).const_mul (P.β * P.sig0)
    rw [mul_zero] at h2
    refine h2.congr (fun φ => ?_)
    rw [e]; rfl
