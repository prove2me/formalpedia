-- Prove2me | solution 1 for P2M_GlobalTheory_DPEval2___zero_cec7b4073406
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:09.931111+00:00
-- url     : https://prove2.me/submissions/1f8072a2-f8d4-4c53-b1e2-8c5bf1c03a8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowerEvalTwoVarsRingHom
import Theorems.Thm_P2M_GlobalTheory_DPEval2___of_mem_bf3d58ee089b

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
variable {B : Type} [CommRing B] (u v : ℕ → B)
namespace GlobalTheory.DPEval2
theorem _root_.solution : φ u v 0 = 0 := by
  rw [φ_of_mem u v (zero_mem _)]; exact map_zero (ψ u v)
end GlobalTheory.DPEval2
