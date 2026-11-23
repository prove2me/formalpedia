-- Prove2me | solution 1 for P2M_GlobalTheory_IndLine_Iwasawa_Grading__q_d9bfcabec8b3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:01.742856+00:00
-- url     : https://prove2.me/submissions/c3893e2b-2811-4690-86ba-4a7ce764469e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul

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
theorem _root_.solution : θ * q = p * θ := by
  calc θ * q = θ * (q * θ) * θ := by rw [mul_assoc, mul_assoc, h.θθ, mul_one]
    _ = p * θ := by rw [← h.θp, ← mul_assoc, h.θθ, one_mul]
end GlobalTheory.IndLine.Iwasawa.Grading
