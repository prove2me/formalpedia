-- Prove2me | solution 1 for P2M_GlobalTheory_IndLine_Iwasawa_Grading__r_de95acebf40e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:54.116338+00:00
-- url     : https://prove2.me/submissions/a8b1a478-dce4-4867-855c-75d409418424

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_Grading__q_d9bfcabec8b3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open GlobalTheory GlobalTheory.IndLine GlobalTheory.IndLine.Iwasawa
variable {R : Type} [Ring R]
open GlobalTheory.IndLine.Iwasawa.Grading
variable {p r q θ : R} (h : Grading p r q θ)
include h
namespace GlobalTheory.IndLine.Iwasawa.Grading
theorem _root_.solution : θ * r = r * θ := by
  rw [h.sum, mul_sub, mul_sub, sub_mul, sub_mul, h.θp, h.θq, mul_one, one_mul]; abel
end GlobalTheory.IndLine.Iwasawa.Grading
