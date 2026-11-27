-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_ringHom_padicAlgCl_ne_zero__274806442fd5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:53:08.091904+00:00
-- url     : https://prove2.me/submissions/ff9ebf5b-00bc-4cb8-83ed-5f2a8f11673f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomPadicAlgClNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomPadicAlgClNeZeroStatement
import Theorems.Thm_GlobalTheory_CurvePoint_exists_ringHom_padicAlgCl_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CharZero B], Finite (ResidueField B) → ∀ h : B, h ≠ 0 → ∃ (p : ℕ) (_ : Fact p.Prime) (χ : B →+* PadicAlgCl p), (∀ b, ‖χ b‖ ≤ 1) ∧ (∀ b ∈ maximalIdeal B, ‖χ b‖ < 1) ∧ χ h ≠ 0 := by
  first | exact @GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero | exact GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero | (intros; apply GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero <;> assumption)
end _root_.GlobalTheory.T
