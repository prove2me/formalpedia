-- Prove2me | solution 1 for P2M_GlobalTheory_DPEval2___of_mem_bf3d58ee089b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:14.309428+00:00
-- url     : https://prove2.me/submissions/27067155-840f-4f71-a5c0-192effb6f3e2

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
variable {B : Type} [CommRing B] (u v : ℕ → B)
namespace GlobalTheory.DPEval2
theorem _root_.solution {q : MvPolynomial (Fin 2) ℚ} (h : q ∈ D) : φ u v q = ψ u v ⟨q, h⟩ := dif_pos h
end GlobalTheory.DPEval2
