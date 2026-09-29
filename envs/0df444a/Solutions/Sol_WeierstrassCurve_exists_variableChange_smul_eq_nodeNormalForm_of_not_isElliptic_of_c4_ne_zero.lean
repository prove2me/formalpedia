-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_smul_eq_nodeNormalForm_of_not_isElliptic_of_c4_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1e12cfb3-f431-58e1-a53c-57050d76cf2c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_nodeNormalForm_of_not_isElliptic_of_c4_ne_zero

set_option maxHeartbeats 6400000
open WeierstrassCurve

theorem solution
    {K : Type*} [Field K] [CharZero K] (W : WeierstrassCurve K)
    (hW : ¬ W.IsElliptic) (hc4 : W.c₄ ≠ 0) :
    ∃ (c : K) (_ : c ≠ 0) (C : WeierstrassCurve.VariableChange K),
      C • W = (⟨0, c, 0, 0, 0⟩ : WeierstrassCurve K) := by
  haveI : Invertible (2:K) := invertibleOfNonzero two_ne_zero
  haveI : Invertible (3:K) := invertibleOfNonzero three_ne_zero
  have hΔ : W.Δ = 0 := by by_contra h; exact hW ⟨isUnit_iff_ne_zero.mpr h⟩

  set W' := W.toShortNF • W with hW'
  have hSNF := W.toShortNF_spec
  have ha1 : W'.a₁ = 0 := hSNF.a₁
  have ha2 : W'.a₂ = 0 := hSNF.a₂
  have ha3 : W'.a₃ = 0 := hSNF.a₃
  have hc4' : W'.c₄ ≠ 0 := by
    rw [hW', variableChange_c₄]; exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hc4
  have hΔ' : W'.Δ = 0 := by rw [hW', variableChange_Δ, hΔ, mul_zero]
  set A := W'.a₄ with hA_def
  set B := W'.a₆ with hB_def

  have hA : A ≠ 0 := by
    intro h; apply hc4'
    have : W'.c₄ = -48 * A := by
      simp only [c₄, b₂, b₄, ha1, ha2, ha3, hA_def]; ring
    rw [this, h, mul_zero]

  have hDisc : 4 * A^3 + 27 * B^2 = 0 := by
    have hΔeq : W'.Δ = -16 * (4 * A^3 + 27 * B^2) := by
      simp only [Δ, b₂, b₄, b₆, b₈, ha1, ha2, ha3, hA_def, hB_def]; ring
    have h16 : (-16 : K) ≠ 0 := by norm_num
    have := hΔ'.symm.trans hΔeq
    exact (mul_eq_zero.mp this.symm).resolve_left h16

  have hB : B ≠ 0 := by
    intro h; apply hA
    have h4A3 : 4 * A^3 = 0 := by
      have hD := hDisc; rw [h] at hD; linear_combination hD
    exact pow_eq_zero_iff (n:=3) (by norm_num) |>.mp
      ((mul_eq_zero.mp h4A3).resolve_left (by norm_num : (4:K) ≠ 0))

  set x₀ := -3 * B / (2 * A) with hx₀
  have h2A : (2:K) * A ≠ 0 := mul_ne_zero two_ne_zero hA

  have hx₀sq : x₀^2 = -A/3 := by
    rw [hx₀]; field_simp; linear_combination hDisc
  have ha4' : A + 3 * x₀^2 = 0 := by rw [hx₀sq]; ring
  have ha6' : B + A * x₀ + x₀^3 = 0 := by
    have : x₀^3 = x₀ * x₀^2 := by ring
    rw [this, hx₀sq, hx₀]; field_simp; ring
  refine ⟨3 * x₀, ?_, ⟨1, x₀, 0, 0⟩ * W.toShortNF, ?_⟩
  ·
    have hc : (3:K) * x₀ = -9 * B / (2 * A) := by rw [hx₀]; ring
    rw [hc]; exact div_ne_zero (mul_ne_zero (by norm_num : (-9:K) ≠ 0) hB) h2A
  · rw [mul_smul, ← hW']
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · simp only [variableChange_a₁, ha1, Units.val_one, inv_one, mul_zero,
        one_mul, add_zero]
    · simp only [variableChange_a₂, ha1, ha2, Units.val_one, inv_one, one_pow,
        one_mul, mul_zero, zero_mul, sub_zero, zero_add]
      ring
    · simp only [variableChange_a₃, ha1, ha3, Units.val_one, inv_one, one_pow,
        one_mul, mul_zero, zero_mul, add_zero]
    · simp only [variableChange_a₄, ha1, ha2, ha3, hA_def, Units.val_one, inv_one,
        one_pow, one_mul, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
      linear_combination ha4'
    · simp only [variableChange_a₆, ha1, ha2, ha3, hA_def, hB_def, Units.val_one,
        inv_one, one_pow, one_mul, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
      linear_combination ha6'

end S_WeierstrassCurve_exists_variableChange_smul_eq_nodeNormalForm_of_not_isElliptic_of_c4_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_nodeNormalForm_of_not_isElliptic_of_c4_ne_zero (solution)
