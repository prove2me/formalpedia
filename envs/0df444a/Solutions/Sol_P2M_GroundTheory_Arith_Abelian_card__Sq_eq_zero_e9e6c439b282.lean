-- Prove2me | solution 1 for P2M_GroundTheory_Arith_Abelian_card__Sq_eq_zero_e9e6c439b282
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:53:14.402695+00:00
-- url     : https://prove2.me/submissions/2ce3f7d5-f48d-4fe3-9fde-ed7afb3eaa94

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Theorems.Thm_GroundTheory_Arith_Abelian_card_zsmul_eq_zero
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian_zsmul_eq_zero_iff__Sq_274c34b39eaa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {n : ℤ} (hn : (n : F) ≠ 0) :
    Nat.card {P : W.toAffine.Point // P = 0 ∨ ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
      P = .some x y h ∧ (W.ΨSq n).eval x = 0} = n.natAbs ^ 2 := by
  rw [← card_zsmul_eq_zero W hn]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun P => (zsmul_eq_zero_iff_ΨSq W n P).symm)
end GroundTheory.Arith.Abelian
