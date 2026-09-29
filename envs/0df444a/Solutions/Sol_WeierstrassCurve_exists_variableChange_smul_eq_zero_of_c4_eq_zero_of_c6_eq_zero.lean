-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_smul_eq_zero_of_c4_eq_zero_of_c6_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fbf58d35-8b99-5afe-b1f7-e942da0db14e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_zero_of_c4_eq_zero_of_c6_eq_zero

set_option maxHeartbeats 6400000
open WeierstrassCurve

theorem solution
    {L : Type*} [Field L] [CharZero L] (W : WeierstrassCurve L)
    (hc4 : W.c₄ = 0) (hc6 : W.c₆ = 0) :
    ∃ C : WeierstrassCurve.VariableChange L,
      C • W = (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve L) := by

  haveI : Invertible (2:L) := invertibleOfNonzero two_ne_zero
  haveI : Invertible (3:L) := invertibleOfNonzero three_ne_zero
  refine ⟨W.toShortNF, ?_⟩
  have hSNF : (W.toShortNF • W).IsShortNF := W.toShortNF_spec

  have hc4' : (W.toShortNF • W).c₄ = 0 := by
    rw [WeierstrassCurve.variableChange_c₄, hc4, mul_zero]
  have hc6' : (W.toShortNF • W).c₆ = 0 := by
    rw [WeierstrassCurve.variableChange_c₆, hc6, mul_zero]

  set W' := W.toShortNF • W with hW'
  have ha1 : W'.a₁ = 0 := hSNF.a₁
  have ha2 : W'.a₂ = 0 := hSNF.a₂
  have ha3 : W'.a₃ = 0 := hSNF.a₃
  have ha4 : W'.a₄ = 0 := by
    have : W'.c₄ = -48 * W'.a₄ := by
      simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, ha1, ha2, ha3]
      ring
    rw [this] at hc4'
    have h48 : (-48:L) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hc4').resolve_left h48
  have ha6 : W'.a₆ = 0 := by
    have : W'.c₆ = -864 * W'.a₆ := by
      simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, ha1, ha2, ha3]
      ring
    rw [this] at hc6'
    have h864 : (-864:L) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hc6').resolve_left h864
  ext <;> simp only [ha1, ha2, ha3, ha4, ha6]

end S_WeierstrassCurve_exists_variableChange_smul_eq_zero_of_c4_eq_zero_of_c6_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_zero_of_c4_eq_zero_of_c6_eq_zero (solution)
