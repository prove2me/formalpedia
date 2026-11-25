-- Prove2me | solution 1 for P2M_GlobalTheory_DPEval2___nsmul_635e58ae52b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:07.475962+00:00
-- url     : https://prove2.me/submissions/e67e47aa-ea3b-4439-bead-d5d82afee404

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowerEvalTwoVarsRingHom
import Theorems.Thm_P2M_GlobalTheory_DPEval2___zsmul_54cdf8776ef8

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
theorem _root_.solution (n : ℕ) {x : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) : φ u v (n • x) = n • φ u v x := by
  rw [← Nat.cast_smul_eq_nsmul ℤ n x, φ_zsmul u v _ hx, Nat.cast_smul_eq_nsmul]
end GlobalTheory.DPEval2
