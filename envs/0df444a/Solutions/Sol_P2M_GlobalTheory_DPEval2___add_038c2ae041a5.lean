-- Prove2me | solution 1 for P2M_GlobalTheory_DPEval2___add_038c2ae041a5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:29.457652+00:00
-- url     : https://prove2.me/submissions/d08202ce-0f2c-4163-b7ac-e745c1cceeec

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
theorem _root_.solution {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) :
    φ u v (x + y) = φ u v x + φ u v y := by
  rw [φ_of_mem u v hx, φ_of_mem u v hy, φ_of_mem u v (add_mem hx hy), ← map_add]; rfl
end GlobalTheory.DPEval2
