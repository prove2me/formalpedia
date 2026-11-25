-- Prove2me | solution 1 for P2M_GroundTheory_Arith_Abelian_zsmul_eq_zero_iff__Sq_274c34b39eaa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:21.5738+00:00
-- url     : https://prove2.me/submissions/8b0fdb97-18cc-4d27-ba74-2f53e709d807

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
import Theorems.Thm_GroundTheory_Arith_Abelian_zsmul_eq_zero_iff
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
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic]
omit [IsSepClosed F] [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (n : ℤ) (P : W.toAffine.Point) :
    n • P = 0 ↔ P = 0 ∨ ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
      P = .some x y h ∧ (W.ΨSq n).eval x = 0 := by
  cases P with
  | zero => rw [← Point.zero_def]; simp
  | some x y h =>
    rw [zsmul_eq_zero_iff W h n]
    constructor
    · intro hx; exact Or.inr ⟨x, y, h, rfl, hx⟩
    · rintro (h0 | ⟨x', y', h', he, hx⟩)
      · exact absurd h0 (Point.some_ne_zero h)
      · rw [Point.some.injEq] at he; rw [he.1]; exact hx
end GroundTheory.Arith.Abelian
