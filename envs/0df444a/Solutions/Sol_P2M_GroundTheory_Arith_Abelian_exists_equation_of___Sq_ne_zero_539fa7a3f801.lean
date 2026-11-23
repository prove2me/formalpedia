-- Prove2me | solution 1 for P2M_GroundTheory_Arith_Abelian_exists_equation_of___Sq_ne_zero_539fa7a3f801
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:43.901796+00:00
-- url     : https://prove2.me/submissions/53504368-b64a-4e92-a56b-e95f984ec925

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution [IsSepClosed F] {x : F} (hx : W.Ψ₂Sq.eval x ≠ 0) :
    ∃ y, W.toAffine.Equation x y := by
  set b := W.a₁ * x + W.a₃
  set c := x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆
  have hD : b ^ 2 + 4 * c = W.Ψ₂Sq.eval x := by
    simp only [Ψ₂Sq, b, c, b₂, b₄, b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    ring
  set q : F[X] := X ^ 2 + C b * X - C c
  have hq' : derivative q = C 2 * X + C b := by
    simp only [q, derivative_sub, derivative_add, derivative_X_pow, derivative_C_mul_X,
      derivative_C]
    simp
  have hsep : q.Separable := by
    rw [Polynomial.separable_def, hq']
    have hD0 : b ^ 2 + 4 * c ≠ 0 := hD ▸ hx
    refine ⟨C (-4 * (b ^ 2 + 4 * c)⁻¹), C (b ^ 2 + 4 * c)⁻¹ * (C 2 * X + C b), ?_⟩
    have e : (C 2 * X + C b) ^ 2 - 4 * q = C (b ^ 2 + 4 * c) := by
      simp only [q, map_add, map_pow, map_mul, map_ofNat]; ring
    calc C (-4 * (b ^ 2 + 4 * c)⁻¹) * q + C (b ^ 2 + 4 * c)⁻¹ * (C 2 * X + C b) * (C 2 * X + C b)
        = C (b ^ 2 + 4 * c)⁻¹ * ((C 2 * X + C b) ^ 2 - 4 * q) := by
          simp only [map_mul, map_neg, map_ofNat]; ring
      _ = 1 := by rw [e, ← C_mul, inv_mul_cancel₀ hD0, C_1]
  have hdeg : q.degree ≠ 0 := by
    have : q.natDegree = 2 := by simp only [q]; compute_degree!
    intro h
    rw [degree_eq_natDegree (fun h0 => by rw [h0] at this; simp at this), this] at h
    exact absurd h (by decide)
  obtain ⟨y, hy⟩ := IsSepClosed.exists_root q hdeg hsep
  refine ⟨y, ?_⟩
  rw [equation_iff]
  simp only [IsRoot, q, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hy
  simp only [b, c] at hy
  linear_combination hy
end GroundTheory.Arith.Abelian
