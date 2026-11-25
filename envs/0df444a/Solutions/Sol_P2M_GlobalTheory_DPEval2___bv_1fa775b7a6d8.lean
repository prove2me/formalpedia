-- Prove2me | solution 1 for P2M_GlobalTheory_DPEval2___bv_1fa775b7a6d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:38:12.047815+00:00
-- url     : https://prove2.me/submissions/e9cd8b34-82d5-4af8-aaea-e24c4337800c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowerEvalTwoVarsRingHom
import Theorems.Thm_P2M_GlobalTheory_DPEval2___eq_74930fdf2648
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
theorem _root_.solution (p : ℕ × ℕ) : φ u v (bv p) = u p.1 * v p.2 := by
  rw [φ_of_mem u v (bv_mem p), ← β_eq, ψ, Module.Basis.constr_basis]
end GlobalTheory.DPEval2
