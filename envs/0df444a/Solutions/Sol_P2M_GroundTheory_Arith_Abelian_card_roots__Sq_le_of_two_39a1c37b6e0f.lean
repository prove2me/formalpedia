-- Prove2me | solution 1 for P2M_GroundTheory_Arith_Abelian_card_roots__Sq_le_of_two_39a1c37b6e0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:25:58.339412+00:00
-- url     : https://prove2.me/submissions/110fa10e-025d-4576-b39a-95a4bdf9558d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Theorems.Thm_GroundTheory_Arith_Abelian_roots_toFinset_sq
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian___Sq_eq_sq_of_two_33556432ac9b
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian__Sq_ne_zero_of_ne_zero_fd3fba5d47fb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [E.IsElliptic]
  (p : ℕ) [hp : Fact p.Prime] [CharP F p]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (h2 : p = 2) : (E.ΨSq p).roots.toFinset.card ≤ 1 := by
  have hne : E.ΨSq p ≠ 0 := ΨSq_ne_zero_of_ne_zero E (by exact_mod_cast hp.out.ne_zero)
  have hΨ : E.ΨSq p = (C E.a₁ * X + C E.a₃) ^ 2 := by
    rw [← Ψ₂Sq_eq_sq_of_two E p h2, h2]; exact ΨSq_two E
  rw [hΨ, roots_toFinset_sq]
  refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
  compute_degree
end GroundTheory.Arith.Abelian
