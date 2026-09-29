-- Prove2me | solution 1 for WeierstrassCurve.mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9806471b-7c9e-53a8-84a7-6a7eda1894f2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero

set_option autoImplicit false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₃_of_isShortNF VariableChange.ext a₃ c₄_of_isShortNF a₁ a₁_of_isShortNF IsShortNF variableChange_a₃ a₂_of_isShortNF a₄ a₂ a₆ variableChange_a₆ variableChange_a₂ variableChange_c₄ variableChange_a₁ variableChange_a₄ c₄ VariableChange"
p2m_open "WeierstrassCurve"

open MulAction

namespace VariableChange
p2m_export "WeierstrassCurve.VariableChange" "u t s r"
p2m_open "WeierstrassCurve.VariableChange"

variable {R : Type*} [CommRing R]

def ofUnit (u : Rˣ) : VariableChange R := ⟨u, 0, 0, 0⟩

@[scoped simp] lemma ofUnit_u (u : Rˣ) : (ofUnit u).u = u := rfl
@[scoped simp] lemma ofUnit_r (u : Rˣ) : (ofUnit u).r = 0 := rfl
@[scoped simp] lemma ofUnit_s (u : Rˣ) : (ofUnit u).s = 0 := rfl
@[scoped simp] lemma ofUnit_t (u : Rˣ) : (ofUnit u).t = 0 := rfl

end VariableChange
p2m_reactivate "P2MW.S_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero.WeierstrassCurve.VariableChange"

section ShortNF

variable {F : Type*} [Field F]

lemma ofUnit_smul_of_isShortNF_of_a₆_eq_zero (E : WeierstrassCurve F) [E.IsShortNF]
    (ha₆ : E.a₆ = 0) {u : Fˣ} (hu : (u : F) ^ 4 = 1) :
    VariableChange.ofUnit u • E = E := by
  have h4 : ((u⁻¹ : Fˣ) : F) ^ 4 = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hu, inv_one]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆, VariableChange.ofUnit_u, VariableChange.ofUnit_r,
      VariableChange.ofUnit_s, VariableChange.ofUnit_t, E.a₁_of_isShortNF,
      E.a₂_of_isShortNF, E.a₃_of_isShortNF, ha₆]
  · ring
  · ring
  · ring
  · linear_combination E.a₄ * h4
  · ring

theorem mem_stabilizer_isShortNF_a₆_eq_zero_iff (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsShortNF] (ha₆ : E.a₆ = 0) (ha₄ : E.a₄ ≠ 0)
    (C : VariableChange F) :
    C ∈ stabilizer (VariableChange F) E ↔
      C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ (C.u : F) ^ 4 = 1 := by
  constructor
  · intro hC
    rw [mem_stabilizer_iff] at hC
    have huinv : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := C.u⁻¹.ne_zero
    have hs : C.s = 0 := by
      have h := congrArg WeierstrassCurve.a₁ hC
      rw [variableChange_a₁, E.a₁_of_isShortNF, zero_add, mul_eq_zero, mul_eq_zero] at h
      exact (h.resolve_left huinv).resolve_left h2
    have hr : C.r = 0 := by
      have h := congrArg WeierstrassCurve.a₂ hC
      rw [variableChange_a₂, E.a₁_of_isShortNF, E.a₂_of_isShortNF, hs] at h
      have h' : ((C.u⁻¹ : Fˣ) : F) ^ 2 * (3 * C.r) = 0 := by linear_combination h
      rw [mul_eq_zero, mul_eq_zero] at h'
      exact (h'.resolve_left (pow_ne_zero 2 huinv)).resolve_left h3
    have ht : C.t = 0 := by
      have h := congrArg WeierstrassCurve.a₃ hC
      rw [variableChange_a₃, E.a₁_of_isShortNF, E.a₃_of_isShortNF, hr, zero_mul, add_zero,
        zero_add, mul_eq_zero, mul_eq_zero] at h
      exact (h.resolve_left (pow_ne_zero 3 huinv)).resolve_left h2
    have hu4 : (C.u : F) ^ 4 = 1 := by
      have h := congrArg WeierstrassCurve.c₄ hC
      rw [variableChange_c₄, Units.val_inv_eq_inv_val, E.c₄_of_isShortNF] at h
      have h48 : (-48 : F) ≠ 0 := fun habs =>
        mul_ne_zero (pow_ne_zero 4 h2) h3 (by linear_combination -habs)
      have h4 : ((C.u : F)⁻¹) ^ 4 = 1 :=
        mul_right_cancel₀ (mul_ne_zero h48 ha₄) (h.trans (one_mul _).symm)
      rw [inv_pow, inv_eq_one] at h4; exact h4
    exact ⟨hr, hs, ht, hu4⟩
  · rintro ⟨hr, hs, ht, hu4⟩
    have hC : C = VariableChange.ofUnit C.u := VariableChange.ext rfl hr hs ht
    rw [mem_stabilizer_iff, hC]
    exact ofUnit_smul_of_isShortNF_of_a₆_eq_zero E ha₆ hu4

end ShortNF
p2m_reactivate "P2MW.S_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero.WeierstrassCurve.VariableChange"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero.WeierstrassCurve.VariableChange P2MW.S_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero.WeierstrassCurve"

theorem solution
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsShortNF] (ha₆ : E.a₆ = 0) (ha₄ : E.a₄ ≠ 0)
    (C : WeierstrassCurve.VariableChange F) :
    C ∈ MulAction.stabilizer (WeierstrassCurve.VariableChange F) E ↔
      C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ (C.u : F) ^ 4 = 1 :=
  WeierstrassCurve.mem_stabilizer_isShortNF_a₆_eq_zero_iff h2 h3 E ha₆ ha₄ C

end S_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero (solution)
