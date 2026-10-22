-- Prove2me | solution 1 for ToneAtTop.Diversion.threshold_A5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:04:33.226596+00:00
-- url     : https://prove2.me/submissions/8debc272-0fb2-46a9-ad7f-325d603dcdeb

import Mathlib
import Definitions.Def_ToneAtTop_Diversion_Model
set_option autoImplicit false
open ToneAtTop.Diversion

theorem solution (P : Params) (hS : P.Standing)
    (hL1a : P.tau < Real.sqrt (2 * P.lam * P.xbar / P.p)) :
    P.tau * P.xbar /
        Real.sqrt (2 * P.lam * P.xbar - P.p * P.tau ^ 2) ≤ P.xbar ↔
      P.tau ≤ Real.sqrt (2 * P.lam * P.xbar / (1 + P.p)) := by
  obtain ⟨hx, hl, hp0, hp1, hβ, hγ, _, hη, _⟩ := hS
  have hτ : 0 < P.tau := by
    unfold Params.tau
    exact div_pos (mul_pos (sub_pos.2 hβ) hη) hγ
  have hlt : P.tau ^ 2 < 2 * P.lam * P.xbar / P.p := (Real.lt_sqrt hτ.le).1 hL1a
  have hlt' : P.p * P.tau ^ 2 < 2 * P.lam * P.xbar := by
    rw [lt_div_iff₀ hp0] at hlt; linarith
  have hpos : 0 < 2 * P.lam * P.xbar - P.p * P.tau ^ 2 := by linarith
  have hs : 0 < Real.sqrt (2 * P.lam * P.xbar - P.p * P.tau ^ 2) := Real.sqrt_pos.2 hpos
  rw [div_le_iff₀ hs]
  have e1 : P.tau * P.xbar ≤ P.xbar * Real.sqrt (2 * P.lam * P.xbar - P.p * P.tau ^ 2) ↔
      P.tau ≤ Real.sqrt (2 * P.lam * P.xbar - P.p * P.tau ^ 2) := by
    rw [mul_comm P.tau, mul_le_mul_iff_right₀ hx]
  rw [e1, Real.le_sqrt' hτ, Real.le_sqrt' hτ, le_div_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith
