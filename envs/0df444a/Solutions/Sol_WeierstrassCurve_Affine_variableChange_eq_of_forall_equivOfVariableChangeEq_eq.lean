-- Prove2me | solution 1 for WeierstrassCurve.Affine.variableChange_eq_of_forall_equivOfVariableChangeEq_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/366e897c-eba7-5f89-9156-dcdb6c47e5e5

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_variableChange_eq_of_forall_equivOfVariableChangeEq_eq

set_option autoImplicit false

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_variableChange_eq_of_forall_equivOfVariableChangeEq_eq.WeierstrassCurve WeierstrassCurve.Affine"

universe u

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ a₄ a₂ a₆ VariableChange"
namespace KB9u
p2m_open "WeierstrassCurve"

variable {F : Type u} [Field F]

theorem exists_equation [IsAlgClosed F] (W : WeierstrassCurve.Affine F) (x : F) : ∃ y : F, W.Equation x y := by
  let p : F[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  have hp : p.degree = 2 := by
    show (X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)).degree = 2
    compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root p (by rw [hp]; decide)
  refine ⟨y, ?_⟩
  rw [equation_iff]
  have h : y ^ 2 + (W.a₁ * x + W.a₃) * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    have h := hy
    simp only [p, IsRoot.def, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at h
    exact h
  linear_combination h

theorem equivOfVariableChangeEq_some [DecidableEq F] (C : VariableChange F) (W : WeierstrassCurve.Affine F)
    {V : WeierstrassCurve.Affine F} (hC : C • W = V) {x y : F} (h : V.Nonsingular x y) :
    ∃ h', Point.equivOfVariableChangeEq hC (Point.some x y h) = Point.some (vcX C x) (vcY C x y) h' := by
  subst hC
  exact ⟨_, rfl⟩

theorem main [DecidableEq F] [IsAlgClosed F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic]
    {C C' : VariableChange F} (hC : C • W₂ = W₁) (hC' : C' • W₂ = W₁)
    (h : ∀ P : W₁.Point, Point.equivOfVariableChangeEq hC P = Point.equivOfVariableChangeEq hC' P) :
    C = C' := by

  have hx : ∀ x y : F, W₁.Equation x y → vcX C x = vcX C' x ∧ vcY C x y = vcY C' x y := by
    intro x y hxy
    have hns : W₁.Nonsingular x y := equation_iff_nonsingular.mp hxy
    have key := h (Point.some x y hns)
    obtain ⟨h₁, e₁⟩ := equivOfVariableChangeEq_some C W₂ hC hns
    obtain ⟨h₂, e₂⟩ := equivOfVariableChangeEq_some C' W₂ hC' hns
    rw [e₁, e₂] at key
    simpa only [Point.some.injEq] using key

  obtain ⟨y₀, h₀⟩ := exists_equation W₁ 0
  obtain ⟨y₁, h₁⟩ := exists_equation W₁ 1
  have hr : C.r = C'.r := by
    have e := (hx 0 y₀ h₀).1
    simp only [vcX, mul_zero, zero_add] at e
    exact e
  have hu2 : (C.u : F) ^ 2 = (C'.u : F) ^ 2 := by
    have e := (hx 1 y₁ h₁).1
    simp only [vcX, mul_one] at e
    rw [hr] at e
    exact add_right_cancel e

  have hlin : ∀ x y : F, W₁.Equation x y →
      ((C.u : F) ^ 3 - (C'.u : F) ^ 3) * y + ((C.u : F) ^ 2 * C.s - (C'.u : F) ^ 2 * C'.s) * x
        + (C.t - C'.t) = 0 := by
    intro x y hxy
    have e := (hx x y hxy).2
    simp only [vcY] at e
    linear_combination e

  have hA0 : (C.u : F) ^ 3 - (C'.u : F) ^ 3 = 0 := by
    by_contra hA0
    set A : F := (C.u : F) ^ 3 - (C'.u : F) ^ 3 with hA
    set B : F := (C.u : F) ^ 2 * C.s - (C'.u : F) ^ 2 * C'.s with hB
    set D : F := C.t - C'.t with hD
    let q : F[X] := Polynomial.C (A ^ 2) * X ^ 3 + Polynomial.C (A ^ 2 * W₁.a₂ - B ^ 2 + W₁.a₁ * A * B) * X ^ 2
      + Polynomial.C (A ^ 2 * W₁.a₄ - 2 * B * D + W₁.a₁ * A * D + W₁.a₃ * A * B) * X
      + Polynomial.C (A ^ 2 * W₁.a₆ - D ^ 2 + W₁.a₃ * A * D)
    have hq : ∀ x : F, q.IsRoot x := by
      intro x
      obtain ⟨y, hxy⟩ := exists_equation W₁ x
      have hl : A * y + B * x + D = 0 := hlin x y hxy
      rw [equation_iff] at hxy
      simp only [q, IsRoot.def, eval_add, eval_mul, eval_pow, eval_C, eval_X]
      linear_combination (-A ^ 2) * hxy + (A * y - (B * x + D) + W₁.a₁ * x * A + W₁.a₃ * A) * hl
    have hq0 : q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      rw [show {x | q.IsRoot x} = Set.univ from Set.eq_univ_of_forall hq]
      exact Set.infinite_univ
    have hc3 : q.coeff 3 = A ^ 2 := by
      simp only [q, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, if_true,
        show ((3 : ℕ) = 2) = False from by decide, show ((1 : ℕ) = 3) = False from by decide,
        show ((3 : ℕ) = 0) = False from by decide, if_false, mul_one, mul_zero, add_zero]
    rw [hq0, coeff_zero] at hc3
    exact hA0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc3.symm)

  have hu3 : (C.u : F) ^ 3 = (C'.u : F) ^ 3 := sub_eq_zero.mp hA0
  have hu : (C.u : F) = (C'.u : F) := by
    have h1 : (C.u : F) ^ 2 ≠ 0 := pow_ne_zero 2 C.u.ne_zero
    have e : (C.u : F) = (C.u : F) ^ 3 / (C.u : F) ^ 2 := by field_simp
    rw [e, hu3, hu2]; field_simp

  have hlin' : ∀ x y : F, W₁.Equation x y →
      ((C.u : F) ^ 2 * C.s - (C'.u : F) ^ 2 * C'.s) * x + (C.t - C'.t) = 0 := by
    intro x y hxy
    have e := hlin x y hxy
    rw [hA0, zero_mul, zero_add] at e
    exact e
  have ht : C.t = C'.t := by
    have e := hlin' 0 y₀ h₀
    rw [mul_zero, zero_add] at e
    exact sub_eq_zero.mp e
  have hs : C.s = C'.s := by
    have e := hlin' 1 y₁ h₁
    rw [ht, sub_self, add_zero, mul_one, hu] at e
    have h1 : (C'.u : F) ^ 2 ≠ 0 := pow_ne_zero 2 C'.u.ne_zero
    have e' : (C'.u : F) ^ 2 * (C.s - C'.s) = 0 := by linear_combination e
    exact sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_left h1)

  rcases C with ⟨u, r, s, t⟩
  rcases C' with ⟨u', r', s', t'⟩
  simp only at hu hr hs ht
  rw [Units.val_inj] at hu
  subst hu; subst hr; subst hs; subst ht
  rfl

end WeierstrassCurve.KB9u

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_Affine_variableChange_eq_of_forall_equivOfVariableChangeEq_eq.WeierstrassCurve WeierstrassCurve.Affine in
theorem solution {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic]
    {C C' : WeierstrassCurve.VariableChange F} (hC : C • W₂ = W₁) (hC' : C' • W₂ = W₁)
    (h : ∀ P : W₁.Point, Point.equivOfVariableChangeEq hC P = Point.equivOfVariableChangeEq hC' P) :
    C = C' :=
  WeierstrassCurve.KB9u.main hC hC' h

end S_WeierstrassCurve_Affine_variableChange_eq_of_forall_equivOfVariableChangeEq_eq
end P2MW
export P2MW.S_WeierstrassCurve_Affine_variableChange_eq_of_forall_equivOfVariableChangeEq_eq (solution)
