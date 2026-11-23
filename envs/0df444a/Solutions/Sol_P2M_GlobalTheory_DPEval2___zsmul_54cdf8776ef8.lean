-- Prove2me | solution 1 for P2M_GlobalTheory_DPEval2___zsmul_54cdf8776ef8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:10.774317+00:00
-- url     : https://prove2.me/submissions/cbac9e93-58f8-4745-af5a-0d6b7a818b33

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
theorem _root_.solution (z : ℤ) {x : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) : φ u v (z • x) = z • φ u v x := by
  rw [φ_of_mem u v hx, φ_of_mem u v (Submodule.smul_mem _ z hx), ← map_zsmul]; rfl
end GlobalTheory.DPEval2
