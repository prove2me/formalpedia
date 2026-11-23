-- Prove2me | solution 1 for P2M_GroundTheory_Arith_Abelian___Sq_ne_zero_d2a733e9e1e7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:48.627054+00:00
-- url     : https://prove2.me/submissions/900ce2bc-a990-4035-8d28-59e7a9e5def7

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
variable {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution : W.Ψ₂Sq ≠ 0 := by
  intro h
  have h3 : (4 : F) = 0 := by rw [← W.coeff_Ψ₂Sq, h, coeff_zero]
  have h2 : W.b₂ = 0 := by
    have := congrArg (coeff · 2) h
    simp only [Ψ₂Sq, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at this
    simpa using this
  have h0 : W.b₆ = 0 := by
    have := congrArg (coeff · 0) h
    simp only [Ψ₂Sq, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at this
    simpa using this
  have hΔ : W.Δ = 0 := by
    rw [Δ, h2, h0]; linear_combination (-2 * W.b₄ ^ 3) * h3
  exact W.isUnit_Δ.ne_zero hΔ
end GroundTheory.Arith.Abelian
