-- Prove2me | solution 1 for P2M_GroundTheory_Arith_Abelian_card_roots__Sq_le_of_odd_33bd30ed21d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:51:00.449905+00:00
-- url     : https://prove2.me/submissions/073f0b6d-c304-45c0-ba00-294951e90144

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Theorems.Thm_GroundTheory_Arith_Abelian_roots_toFinset_sq
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian__Sq_ne_zero_of_ne_zero_fd3fba5d47fb
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
theorem _root_.solution (hodd : p ≠ 2) :
    (E.ΨSq p).roots.toFinset.card ≤ (p ^ 2 - 1) / 2 - 1 := by
  have hpodd : ¬ Even (p : ℤ) := by
    rw [Int.even_coe_nat]
    exact fun h => hodd ((Nat.Prime.even_iff hp.out).mp h)
  have hΨ : E.ΨSq p = E.preΨ p ^ 2 := by
    rw [ΨSq, if_neg hpodd, mul_one]
  have hne : E.ΨSq p ≠ 0 := ΨSq_ne_zero_of_ne_zero E (by exact_mod_cast hp.out.ne_zero)
  have hpre : E.preΨ p ≠ 0 := fun h => hne (by rw [hΨ, h]; ring)
  rw [hΨ, roots_toFinset_sq]
  refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
  have hle := E.natDegree_preΨ_le p
  have hco := E.coeff_preΨ p
  simp only [Int.natAbs_natCast, if_neg hpodd] at hle hco
  have hc0 : (E.preΨ p).coeff ((p ^ 2 - 1) / 2) = 0 := by
    rw [hco]; exact_mod_cast CharP.cast_eq_zero F p
  have hlt : (E.preΨ p).natDegree ≠ (p ^ 2 - 1) / 2 := by
    intro h
    apply hpre
    rw [← leadingCoeff_eq_zero, leadingCoeff, h, hc0]
  omega
end GroundTheory.Arith.Abelian
