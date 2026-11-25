-- Prove2me | solution 1 for PI.EF.norm_logDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:42:35.554865+00:00
-- url     : https://prove2.me/submissions/8b4c3ad9-516c-44be-8d2c-942bc6d8351f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBounds
import Theorems.Thm_PI_EF_norm_root_number_le_one
import Theorems.Thm_PI_EF_norm_character_correction_le
import Theorems.Thm_PI_EF_norm_near_sum_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.EF
open Complex DirichletCharacter
private lemma norm_le_add_add_four_of_norm_sub_le {a b c e : ℂ} {x y : ℝ} (h1 : ‖a - b - c + e‖ ≤ x) (h2 : ‖b‖ ≤ y)
    (h3 : ‖c‖ ≤ 2) (h4 : ‖e‖ ≤ 2) : ‖a‖ ≤ x + y + 4 := by
  have e1 : a = (a - b - c + e) + b + c - e := by ring
  rw [e1]
  have k1 := norm_sub_le ((a - b - c + e) + b + c) e
  have k2 := norm_add_le ((a - b - c + e) + b) c
  have k3 := norm_add_le (a - b - c + e) b
  linarith
end PI.EF
end
end

set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex DirichletCharacter
namespace PI.EF
theorem _root_.solution {Cw Cl : ℝ} (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3)
    (h0 : LFunction χ s ≠ 0) (hs0 : 1 / 2 ≤ ‖s‖) (hs1 : 1 / 2 ≤ ‖s - 1‖) {d : ℝ} (hd : 0 < d)
    (h : ∀ ρ ∈ ZerosNear χ s.im, d ≤ ‖s - ρ‖) :
    ‖logDeriv (LFunction χ) s‖ ≤
      Cl * Real.log (N * (|s.im| + 2)) + Cw * Real.log (N * (|s.im| + 2)) / d + 4 := by
  have hs1' : s ≠ 1 := by
    rintro rfl
    norm_num at hs1
  have hmain := hL N χ hχ s h1 h2 h0 hs1'
  have hsum := norm_near_sum_le hW χ hχ s hd h
  have hE : ‖eps0 χ / s‖ ≤ 2 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith [norm_root_number_le_one χ]
  have hD : ‖del1 χ / (s - 1)‖ ≤ 2 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith [norm_character_correction_le χ]
  exact norm_le_add_add_four_of_norm_sub_le hmain hsum hE hD
end PI.EF
