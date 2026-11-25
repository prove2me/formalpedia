-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ProdUnitInert.y_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:23.047735+00:00
-- url     : https://prove2.me/submissions/82673c78-82b8-46b6-8da8-1540935728d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_NatCastNormLeOne
import Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_not_small_sq_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_natCast_norm_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ProdUnitInert
variable {p : ℕ} [Fact p.Prime]
namespace PI.UnitaryGroupMassFormula.ProdUnitInert
theorem _root_.solution (d : ℕ) (hd : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p))) (X Y : ℚ_[p])
    (h : X ^ 2 + d * Y ^ 2 = 1) : ‖Y‖ ≤ 1 := by
  by_contra hY
  push Not at hY
  have hY0 : Y ≠ 0 := by
    rintro rfl
    simp at hY
    linarith
  have key : (X / Y) ^ 2 + d = 1 / Y ^ 2 := by
    rw [div_pow]
    field_simp
    linear_combination h
  have hsmall : ‖(X / Y) ^ 2 + (d : ℚ_[p])‖ < 1 := by
    rw [key, norm_div, norm_one, norm_pow]
    have : 1 < ‖Y‖ ^ 2 := by nlinarith
    rw [div_lt_one (by linarith)]
    exact this
  have ht1 : ‖X / Y‖ ≤ 1 := by
    by_contra ht1
    push Not at ht1
    have h2 : 1 < ‖(X / Y) ^ 2‖ := by rw [norm_pow]; nlinarith
    have hd1 := natCast_norm_le_one (p := p) d
    have hne : ‖(X / Y) ^ 2‖ ≠ ‖(d : ℚ_[p])‖ := by intro h'; linarith
    rw [Padic.add_eq_max_of_ne hne] at hsmall
    have := le_max_left ‖(X / Y) ^ 2‖ ‖(d : ℚ_[p])‖
    linarith
  let T : ℤ_[p] := ⟨X / Y, ht1⟩
  apply not_small_sq_add d hd T
  have hc : (((T ^ 2 + (d : ℤ_[p]) : ℤ_[p])) : ℚ_[p]) = (X / Y) ^ 2 + d := by
    have hT : (T : ℚ_[p]) = X / Y := rfl
    rw [PadicInt.coe_add, PadicInt.coe_pow, hT, PadicInt.coe_natCast]
  rw [PadicInt.norm_def, hc]
  exact hsmall
end PI.UnitaryGroupMassFormula.ProdUnitInert
