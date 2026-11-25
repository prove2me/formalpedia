-- Prove2me | solution 1 for P2M_GlobalTheory_T_pic_pi_isOfFinOrder__3e36705ac5d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:33:50.153043+00:00
-- url     : https://prove2.me/submissions/159ed4ab-cbfd-49b3-9fc5-59c37eb41b68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicPiIsOfFinOrder
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicPiIsOfFinOrderStatement
import Theorems.Thm_GlobalTheory_pic_pi_isOfFinOrder


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
theorem _root_.solution : ∀ (ι : Type) [Finite ι] (R : ι → Type) [∀ i, CommRing (R i)], (∀ i (M : CommRing.Pic (R i)), IsOfFinOrder M) → ∀ M : CommRing.Pic ((i : ι) → R i), IsOfFinOrder M := by
  first | exact @GlobalTheory.pic_pi_isOfFinOrder | exact GlobalTheory.pic_pi_isOfFinOrder | (intros; apply GlobalTheory.pic_pi_isOfFinOrder <;> assumption)
end _root_.GlobalTheory.T
