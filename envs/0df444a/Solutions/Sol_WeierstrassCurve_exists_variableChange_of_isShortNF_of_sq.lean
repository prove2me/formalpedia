-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_of_isShortNF_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/bbeaa595-dd8d-5cfa-8efa-d5b8f98719c7

import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_of_isShortNF_of_sq

open WeierstrassCurve

theorem solution {F : Type*} [Field F] (E E' : WeierstrassCurve F)
    [E.IsShortNF] [E'.IsShortNF]
    (ha₄ : E.a₄ ≠ 0) (ha₆ : E.a₆ ≠ 0) (ha₄' : E'.a₄ ≠ 0) (ha₆' : E'.a₆ ≠ 0)
    (hrel : E.a₄ ^ 3 * E'.a₆ ^ 2 = E'.a₄ ^ 3 * E.a₆ ^ 2)
    {s : F} (hs : s ^ 2 * (E'.a₆ * E.a₄) = E.a₆ * E'.a₄) :
    ∃ C : VariableChange F, C • E = E' := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, zero_mul] at hs
    exact mul_ne_zero ha₆ ha₄' hs.symm

  have hu4 : s ^ 4 * E'.a₄ = E.a₄ := by
    have h2' : s ^ 4 * E'.a₄ * (E'.a₆ * E.a₄) ^ 2 = E.a₄ * (E'.a₆ * E.a₄) ^ 2 := by
      linear_combination (E'.a₄ * (s ^ 2 * E'.a₆ * E.a₄ + E.a₆ * E'.a₄)) * hs - hrel
    exact mul_right_cancel₀ (pow_ne_zero 2 (mul_ne_zero ha₆' ha₄)) h2'
  have hu6 : s ^ 6 * E'.a₆ = E.a₆ := by
    have h3' : s ^ 6 * E'.a₆ * (E'.a₄ * E.a₄) = E.a₆ * (E'.a₄ * E.a₄) := by
      linear_combination (s ^ 2 * E'.a₆ * E.a₄) * hu4 + E.a₄ * hs
    exact mul_right_cancel₀ (mul_ne_zero ha₄' ha₄) h3'
  refine ⟨⟨Units.mk0 s hs0, 0, 0, 0⟩, ?_⟩
  ext
  ·
    rw [variableChange_a₁, E.a₁_of_isShortNF, E'.a₁_of_isShortNF,
      show (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange F).s = 0 from rfl]
    ring
  ·
    rw [variableChange_a₂, E.a₂_of_isShortNF, E'.a₂_of_isShortNF, E.a₁_of_isShortNF,
      show (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange F).s = 0 from rfl,
      show (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange F).r = 0 from rfl]
    ring
  ·
    rw [variableChange_a₃, E.a₃_of_isShortNF, E'.a₃_of_isShortNF, E.a₁_of_isShortNF,
      show (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange F).r = 0 from rfl,
      show (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange F).t = 0 from rfl]
    ring
  ·
    rw [variableChange_a₄,
      show (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange F).r = 0 from rfl,
      show (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange F).s = 0 from rfl,
      show (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange F).t = 0 from rfl,
      show (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange F).u = Units.mk0 s hs0 from rfl,
      Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, inv_mul_eq_div,
      div_eq_iff (pow_ne_zero 4 hs0)]
    linear_combination -hu4
  ·
    rw [variableChange_a₆,
      show (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange F).r = 0 from rfl,
      show (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange F).t = 0 from rfl,
      show (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange F).u = Units.mk0 s hs0 from rfl,
      Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, inv_mul_eq_div,
      div_eq_iff (pow_ne_zero 6 hs0)]
    linear_combination -hu6

end S_WeierstrassCurve_exists_variableChange_of_isShortNF_of_sq
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_of_isShortNF_of_sq (solution)
