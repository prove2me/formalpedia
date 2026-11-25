-- Prove2me | solution 1 for PI.ZW.rootNumber_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:24:14.538687+00:00
-- url     : https://prove2.me/submissions/1c83ebeb-dc87-4648-9051-91b176929d48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open PI PI.ZW
open DirichletCharacter
namespace PI.ZW
theorem _root_.solution {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    rootNumber χ ≠ 0 := by
  intro h
  have h2 := hχ.completedLFunction_one_sub (-1)
  rw [h] at h2
  simp only [mul_zero, zero_mul] at h2
  norm_num at h2
  have hne := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num : (2 : ℂ) ≠ 1))
    (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re)
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 2 (Or.inl two_ne_zero), h2, zero_div] at hne
  exact hne rfl
end PI.ZW
