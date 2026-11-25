-- Prove2me | solution 1 for P2M_GlobalTheory_T_pic_isOfFinOrder_of_finite_int__b828631832c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:33:40.465805+00:00
-- url     : https://prove2.me/submissions/d632051b-e18d-49e8-ab1f-69964e666e44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicIsOfFinOrderOfFiniteInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicIsOfFinOrderOfFiniteIntStatement
import Theorems.Thm_GlobalTheory_pic_isOfFinOrder_of_finite_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] (M : CommRing.Pic B), IsOfFinOrder M := by
  first | exact @GlobalTheory.pic_isOfFinOrder_of_finite_int | exact GlobalTheory.pic_isOfFinOrder_of_finite_int | (intros; apply GlobalTheory.pic_isOfFinOrder_of_finite_int <;> assumption)
end _root_.GlobalTheory.T
