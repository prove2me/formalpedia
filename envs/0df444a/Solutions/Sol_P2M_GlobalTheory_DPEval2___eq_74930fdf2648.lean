-- Prove2me | solution 1 for P2M_GlobalTheory_DPEval2___eq_74930fdf2648
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:05.151847+00:00
-- url     : https://prove2.me/submissions/cea6a943-3407-476e-b6b1-04719f1329a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowerEvalTwoVarsRingHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DPEval2
namespace GlobalTheory.DPEval2
theorem _root_.solution (p : ℕ × ℕ) : β p = ⟨bv p, bv_mem p⟩ :=
  Module.Basis.span_apply _ p
end GlobalTheory.DPEval2
