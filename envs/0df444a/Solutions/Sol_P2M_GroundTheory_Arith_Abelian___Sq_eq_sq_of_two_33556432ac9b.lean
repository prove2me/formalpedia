-- Prove2me | solution 1 for P2M_GroundTheory_Arith_Abelian___Sq_eq_sq_of_two_33556432ac9b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:51:35.676258+00:00
-- url     : https://prove2.me/submissions/f6a621cb-8f1b-4de5-a85c-fb0887313359

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
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
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [E.IsElliptic]
  (p : ℕ) [hp : Fact p.Prime] [CharP F p]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (h2 : p = 2) : E.Ψ₂Sq = (C E.a₁ * X + C E.a₃) ^ 2 := by
  subst h2
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have h2X : (2 : F[X]) = 0 := by rw [← C_ofNat, h2F, C_0]
  have e : E.Ψ₂Sq = (C E.a₁ * X + C E.a₃) ^ 2 + 2 * (2 * X ^ 3 + C (2 * E.a₂) * X ^ 2 +
      C E.b₄ * X - C E.a₁ * C E.a₃ * X + C (2 * E.a₆)) := by
    simp only [Ψ₂Sq, b₂, b₆, map_add, map_mul, map_pow, map_ofNat]
    ring
  rw [e, h2X, zero_mul, add_zero]
end GroundTheory.Arith.Abelian
